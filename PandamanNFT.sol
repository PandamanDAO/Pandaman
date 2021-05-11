// File: @openzeppelin/contracts/utils/introspection/IERC165.sol

// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC165 standard, as defined in the
 * https://eips.ethereum.org/EIPS/eip-165[EIP].
 *
 * Implementers can declare support of contract interfaces, which can then be
 * queried by others ({ERC165Checker}).
 *
 * For an implementation, see {ERC165}.
 */
interface IERC165 {
    /**
     * @dev Returns true if this contract implements the interface defined by
     * `interfaceId`. See the corresponding
     * https://eips.ethereum.org/EIPS/eip-165#how-interfaces-are-identified[EIP section]
     * to learn more about how these ids are created.
     *
     * This function call must use less than 30 000 gas.
     */
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

// File: @openzeppelin/contracts/token/ERC1155/IERC1155.sol



pragma solidity ^0.8.0;


/**
 * @dev Required interface of an ERC1155 compliant contract, as defined in the
 * https://eips.ethereum.org/EIPS/eip-1155[EIP].
 *
 * _Available since v3.1._
 */
interface IERC1155 is IERC165 {
    /**
     * @dev Emitted when `value` tokens of token type `id` are transferred from `from` to `to` by `operator`.
     */
    event TransferSingle(address indexed operator, address indexed from, address indexed to, uint256 id, uint256 value);

    /**
     * @dev Equivalent to multiple {TransferSingle} events, where `operator`, `from` and `to` are the same for all
     * transfers.
     */
    event TransferBatch(address indexed operator, address indexed from, address indexed to, uint256[] ids, uint256[] values);

    /**
     * @dev Emitted when `account` grants or revokes permission to `operator` to transfer their tokens, according to
     * `approved`.
     */
    event ApprovalForAll(address indexed account, address indexed operator, bool approved);

    /**
     * @dev Emitted when the URI for token type `id` changes to `value`, if it is a non-programmatic URI.
     *
     * If an {URI} event was emitted for `id`, the standard
     * https://eips.ethereum.org/EIPS/eip-1155#metadata-extensions[guarantees] that `value` will equal the value
     * returned by {IERC1155MetadataURI-uri}.
     */
    event URI(string value, uint256 indexed id);

    /**
     * @dev Returns the amount of tokens of token type `id` owned by `account`.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function balanceOf(address account, uint256 id) external view returns (uint256);

    /**
     * @dev xref:ROOT:erc1155.adoc#batch-operations[Batched] version of {balanceOf}.
     *
     * Requirements:
     *
     * - `accounts` and `ids` must have the same length.
     */
    function balanceOfBatch(address[] calldata accounts, uint256[] calldata ids) external view returns (uint256[] memory);

    /**
     * @dev Grants or revokes permission to `operator` to transfer the caller's tokens, according to `approved`,
     *
     * Emits an {ApprovalForAll} event.
     *
     * Requirements:
     *
     * - `operator` cannot be the caller.
     */
    function setApprovalForAll(address operator, bool approved) external;

    /**
     * @dev Returns true if `operator` is approved to transfer ``account``'s tokens.
     *
     * See {setApprovalForAll}.
     */
    function isApprovedForAll(address account, address operator) external view returns (bool);

    /**
     * @dev Transfers `amount` tokens of token type `id` from `from` to `to`.
     *
     * Emits a {TransferSingle} event.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     * - If the caller is not `from`, it must be have been approved to spend ``from``'s tokens via {setApprovalForAll}.
     * - `from` must have a balance of tokens of type `id` of at least `amount`.
     * - If `to` refers to a smart contract, it must implement {IERC1155Receiver-onERC1155Received} and return the
     * acceptance magic value.
     */
    function safeTransferFrom(address from, address to, uint256 id, uint256 amount, bytes calldata data) external;

    /**
     * @dev xref:ROOT:erc1155.adoc#batch-operations[Batched] version of {safeTransferFrom}.
     *
     * Emits a {TransferBatch} event.
     *
     * Requirements:
     *
     * - `ids` and `amounts` must have the same length.
     * - If `to` refers to a smart contract, it must implement {IERC1155Receiver-onERC1155BatchReceived} and return the
     * acceptance magic value.
     */
    function safeBatchTransferFrom(address from, address to, uint256[] calldata ids, uint256[] calldata amounts, bytes calldata data) external;
}

// File: @openzeppelin/contracts/token/ERC1155/IERC1155Receiver.sol



pragma solidity ^0.8.0;


/**
 * _Available since v3.1._
 */
interface IERC1155Receiver is IERC165 {

    /**
        @dev Handles the receipt of a single ERC1155 token type. This function is
        called at the end of a `safeTransferFrom` after the balance has been updated.
        To accept the transfer, this must return
        `bytes4(keccak256("onERC1155Received(address,address,uint256,uint256,bytes)"))`
        (i.e. 0xf23a6e61, or its own function selector).
        @param operator The address which initiated the transfer (i.e. msg.sender)
        @param from The address which previously owned the token
        @param id The ID of the token being transferred
        @param value The amount of tokens being transferred
        @param data Additional data with no specified format
        @return `bytes4(keccak256("onERC1155Received(address,address,uint256,uint256,bytes)"))` if transfer is allowed
    */
    function onERC1155Received(
        address operator,
        address from,
        uint256 id,
        uint256 value,
        bytes calldata data
    )
        external
        returns(bytes4);

    /**
        @dev Handles the receipt of a multiple ERC1155 token types. This function
        is called at the end of a `safeBatchTransferFrom` after the balances have
        been updated. To accept the transfer(s), this must return
        `bytes4(keccak256("onERC1155BatchReceived(address,address,uint256[],uint256[],bytes)"))`
        (i.e. 0xbc197c81, or its own function selector).
        @param operator The address which initiated the batch transfer (i.e. msg.sender)
        @param from The address which previously owned the token
        @param ids An array containing ids of each token being transferred (order and length must match values array)
        @param values An array containing amounts of each token being transferred (order and length must match ids array)
        @param data Additional data with no specified format
        @return `bytes4(keccak256("onERC1155BatchReceived(address,address,uint256[],uint256[],bytes)"))` if transfer is allowed
    */
    function onERC1155BatchReceived(
        address operator,
        address from,
        uint256[] calldata ids,
        uint256[] calldata values,
        bytes calldata data
    )
        external
        returns(bytes4);
}

// File: @openzeppelin/contracts/token/ERC1155/extensions/IERC1155MetadataURI.sol



pragma solidity ^0.8.0;


/**
 * @dev Interface of the optional ERC1155MetadataExtension interface, as defined
 * in the https://eips.ethereum.org/EIPS/eip-1155#metadata-extensions[EIP].
 *
 * _Available since v3.1._
 */
interface IERC1155MetadataURI is IERC1155 {
    /**
     * @dev Returns the URI for token type `id`.
     *
     * If the `\{id\}` substring is present in the URI, it must be replaced by
     * clients with the actual token type ID.
     */
    function uri(uint256 id) external view returns (string memory);
}

// File: @openzeppelin/contracts/utils/Address.sol



pragma solidity ^0.8.0;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly { size := extcodesize(account) }
        return size > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: value }(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data, string memory errorMessage) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(bool success, bytes memory returndata, string memory errorMessage) private pure returns(bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

// File: @openzeppelin/contracts/utils/Context.sol



pragma solidity ^0.8.0;

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

// File: @openzeppelin/contracts/utils/introspection/ERC165.sol



pragma solidity ^0.8.0;


/**
 * @dev Implementation of the {IERC165} interface.
 *
 * Contracts that want to implement ERC165 should inherit from this contract and override {supportsInterface} to check
 * for the additional interface id that will be supported. For example:
 *
 * ```solidity
 * function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
 *     return interfaceId == type(MyInterface).interfaceId || super.supportsInterface(interfaceId);
 * }
 * ```
 *
 * Alternatively, {ERC165Storage} provides an easier to use but more expensive implementation.
 */
abstract contract ERC165 is IERC165 {
    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
        return interfaceId == type(IERC165).interfaceId;
    }
}

// File: @openzeppelin/contracts/token/ERC1155/ERC1155.sol



pragma solidity ^0.8.0;







/**
 *
 * @dev Implementation of the basic standard multi-token.
 * See https://eips.ethereum.org/EIPS/eip-1155
 * Originally based on code by Enjin: https://github.com/enjin/erc-1155
 *
 * _Available since v3.1._
 */
contract ERC1155 is Context, ERC165, IERC1155, IERC1155MetadataURI,IERC1155Receiver {
    using Address for address;

    // Mapping from token ID to account balances
    mapping (uint256 => mapping(address => uint256)) private _balances;

    // Mapping from account to operator approvals
    mapping (address => mapping(address => bool)) private _operatorApprovals;

    // Used as the URI for all token types by relying on ID substitution, e.g. https://token-cdn-domain/{id}.json
    string private _uri;

    /**
     * @dev See {_setURI}.
     */
    constructor (string memory uri_) {
        _setURI(uri_);
    }
    
    function onERC1155Received(address, address, uint256, uint256, bytes calldata)
        public view virtual override
        returns(bytes4)
    {
        return 0xf23a6e61;
    }

    function onERC1155BatchReceived(address, address, uint256[] calldata, uint256[] calldata, bytes calldata)
        public view virtual override
        returns(bytes4)
    {
        return 0xbc197c81;
    }

    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override(ERC165, IERC165) returns (bool) {
        return interfaceId == type(IERC1155).interfaceId
            || interfaceId == type(IERC1155MetadataURI).interfaceId
            || super.supportsInterface(interfaceId);
    }

    /**
     * @dev See {IERC1155MetadataURI-uri}.
     *
     * This implementation returns the same URI for *all* token types. It relies
     * on the token type ID substitution mechanism
     * https://eips.ethereum.org/EIPS/eip-1155#metadata[defined in the EIP].
     *
     * Clients calling this function must replace the `\{id\}` substring with the
     * actual token type ID.
     */
    function uri(uint256) public view virtual override returns (string memory) {
        return _uri;
    }

    /**
     * @dev See {IERC1155-balanceOf}.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function balanceOf(address account, uint256 id) public view virtual override returns (uint256) {
        require(account != address(0), "ERC1155: balance query for the zero address");
        return _balances[id][account];
    }

    /**
     * @dev See {IERC1155-balanceOfBatch}.
     *
     * Requirements:
     *
     * - `accounts` and `ids` must have the same length.
     */
    function balanceOfBatch(
        address[] memory accounts,
        uint256[] memory ids
    )
        public
        view
        virtual
        override
        returns (uint256[] memory)
    {
        require(accounts.length == ids.length, "ERC1155: accounts and ids length mismatch");

        uint256[] memory batchBalances = new uint256[](accounts.length);

        for (uint256 i = 0; i < accounts.length; ++i) {
            batchBalances[i] = balanceOf(accounts[i], ids[i]);
        }

        return batchBalances;
    }

    /**
     * @dev See {IERC1155-setApprovalForAll}.
     */
    function setApprovalForAll(address operator, bool approved) public virtual override {
        require(_msgSender() != operator, "ERC1155: setting approval status for self");

        _operatorApprovals[_msgSender()][operator] = approved;
        emit ApprovalForAll(_msgSender(), operator, approved);
    }
    

    /**
     * @dev See {IERC1155-isApprovedForAll}.
     */
    function isApprovedForAll(address account, address operator) public view virtual override returns (bool) {
        return _operatorApprovals[account][operator];
    }

    /**
     * @dev See {IERC1155-safeTransferFrom}.
     */
    function safeTransferFrom(
        address from,
        address to,
        uint256 id,
        uint256 amount,
        bytes memory data
    )
        public
        virtual
        override
    {
        require(to != address(0), "ERC1155: transfer to the zero address");
        require(
            from == _msgSender() || isApprovedForAll(from, _msgSender()),
            "ERC1155: caller is not owner nor approved"
        );

        address operator = _msgSender();

        _beforeTokenTransfer(operator, from, to, _asSingletonArray(id), _asSingletonArray(amount), data);

        uint256 fromBalance = _balances[id][from];
        require(fromBalance >= amount, "ERC1155: insufficient balance for transfer");
        _balances[id][from] = fromBalance - amount;
        _balances[id][to] += amount;

        emit TransferSingle(operator, from, to, id, amount);

        _doSafeTransferAcceptanceCheck(operator, from, to, id, amount, data);
    }
    
    function _saleTransfer(
        address from,
        address to,
        uint256 id,
        uint256 amount,
        bytes memory data
    )
        internal
    {
        require(to != address(0), "ERC1155: transfer to the zero address");

        address operator = _msgSender();

        _beforeTokenTransfer(operator, from, to, _asSingletonArray(id), _asSingletonArray(amount), data);

        uint256 fromBalance = _balances[id][from];
        require(fromBalance >= amount, "ERC1155: insufficient balance for transfer");
        _balances[id][from] = fromBalance - amount;
        _balances[id][to] += amount;

        emit TransferSingle(operator, from, to, id, amount);

        _doSafeTransferAcceptanceCheck(operator, from, to, id, amount, data);
    }

    /**
     * @dev See {IERC1155-safeBatchTransferFrom}.
     */
    function safeBatchTransferFrom(
        address from,
        address to,
        uint256[] memory ids,
        uint256[] memory amounts,
        bytes memory data
    )
        public
        virtual
        override
    {
        require(ids.length == amounts.length, "ERC1155: ids and amounts length mismatch");
        require(to != address(0), "ERC1155: transfer to the zero address");
        require(
            from == _msgSender() || isApprovedForAll(from, _msgSender()),
            "ERC1155: transfer caller is not owner nor approved"
        );

        address operator = _msgSender();

        _beforeTokenTransfer(operator, from, to, ids, amounts, data);

        for (uint256 i = 0; i < ids.length; ++i) {
            uint256 id = ids[i];
            uint256 amount = amounts[i];

            uint256 fromBalance = _balances[id][from];
            require(fromBalance >= amount, "ERC1155: insufficient balance for transfer");
            _balances[id][from] = fromBalance - amount;
            _balances[id][to] += amount;
        }

        emit TransferBatch(operator, from, to, ids, amounts);

        _doSafeBatchTransferAcceptanceCheck(operator, from, to, ids, amounts, data);
    }

    /**
     * @dev Sets a new URI for all token types, by relying on the token type ID
     * substitution mechanism
     * https://eips.ethereum.org/EIPS/eip-1155#metadata[defined in the EIP].
     *
     * By this mechanism, any occurrence of the `\{id\}` substring in either the
     * URI or any of the amounts in the JSON file at said URI will be replaced by
     * clients with the token type ID.
     *
     * For example, the `https://token-cdn-domain/\{id\}.json` URI would be
     * interpreted by clients as
     * `https://token-cdn-domain/000000000000000000000000000000000000000000000000000000000004cce0.json`
     * for token type ID 0x4cce0.
     *
     * See {uri}.
     *
     * Because these URIs cannot be meaningfully represented by the {URI} event,
     * this function emits no events.
     */
    function _setURI(string memory newuri) internal virtual {
        _uri = newuri;
    }

    /**
     * @dev Creates `amount` tokens of token type `id`, and assigns them to `account`.
     *
     * Emits a {TransferSingle} event.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - If `account` refers to a smart contract, it must implement {IERC1155Receiver-onERC1155Received} and return the
     * acceptance magic value.
     */
    function _mint(address account, uint256 id, uint256 amount, bytes memory data) internal virtual {
        require(account != address(0), "ERC1155: mint to the zero address");

        address operator = _msgSender();

        _beforeTokenTransfer(operator, address(0), account, _asSingletonArray(id), _asSingletonArray(amount), data);

        _balances[id][account] += amount;
        emit TransferSingle(operator, address(0), account, id, amount);

        _doSafeTransferAcceptanceCheck(operator, address(0), account, id, amount, data);
    }

    /**
     * @dev xref:ROOT:erc1155.adoc#batch-operations[Batched] version of {_mint}.
     *
     * Requirements:
     *
     * - `ids` and `amounts` must have the same length.
     * - If `to` refers to a smart contract, it must implement {IERC1155Receiver-onERC1155BatchReceived} and return the
     * acceptance magic value.
     */
    function _mintBatch(address to, uint256[] memory ids, uint256[] memory amounts, bytes memory data) internal virtual {
        require(to != address(0), "ERC1155: mint to the zero address");
        require(ids.length == amounts.length, "ERC1155: ids and amounts length mismatch");

        address operator = _msgSender();

        _beforeTokenTransfer(operator, address(0), to, ids, amounts, data);

        for (uint i = 0; i < ids.length; i++) {
            _balances[ids[i]][to] += amounts[i];
        }

        emit TransferBatch(operator, address(0), to, ids, amounts);

        _doSafeBatchTransferAcceptanceCheck(operator, address(0), to, ids, amounts, data);
    }

    /**
     * @dev Destroys `amount` tokens of token type `id` from `account`
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens of token type `id`.
     */
    function _burn(address account, uint256 id, uint256 amount) internal virtual {
        require(account != address(0), "ERC1155: burn from the zero address");

        address operator = _msgSender();

        _beforeTokenTransfer(operator, account, address(0), _asSingletonArray(id), _asSingletonArray(amount), "");

        uint256 accountBalance = _balances[id][account];
        require(accountBalance >= amount, "ERC1155: burn amount exceeds balance");
        _balances[id][account] = accountBalance - amount;

        emit TransferSingle(operator, account, address(0), id, amount);
    }

    /**
     * @dev xref:ROOT:erc1155.adoc#batch-operations[Batched] version of {_burn}.
     *
     * Requirements:
     *
     * - `ids` and `amounts` must have the same length.
     */
    function _burnBatch(address account, uint256[] memory ids, uint256[] memory amounts) internal virtual {
        require(account != address(0), "ERC1155: burn from the zero address");
        require(ids.length == amounts.length, "ERC1155: ids and amounts length mismatch");

        address operator = _msgSender();

        _beforeTokenTransfer(operator, account, address(0), ids, amounts, "");

        for (uint i = 0; i < ids.length; i++) {
            uint256 id = ids[i];
            uint256 amount = amounts[i];

            uint256 accountBalance = _balances[id][account];
            require(accountBalance >= amount, "ERC1155: burn amount exceeds balance");
            _balances[id][account] = accountBalance - amount;
        }

        emit TransferBatch(operator, account, address(0), ids, amounts);
    }

    /**
     * @dev Hook that is called before any token transfer. This includes minting
     * and burning, as well as batched variants.
     *
     * The same hook is called on both single and batched variants. For single
     * transfers, the length of the `id` and `amount` arrays will be 1.
     *
     * Calling conditions (for each `id` and `amount` pair):
     *
     * - When `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * of token type `id` will be  transferred to `to`.
     * - When `from` is zero, `amount` tokens of token type `id` will be minted
     * for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens of token type `id`
     * will be burned.
     * - `from` and `to` are never both zero.
     * - `ids` and `amounts` have the same, non-zero length.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(
        address operator,
        address from,
        address to,
        uint256[] memory ids,
        uint256[] memory amounts,
        bytes memory data
    )
        internal
        virtual
    { }

    function _doSafeTransferAcceptanceCheck(
        address operator,
        address from,
        address to,
        uint256 id,
        uint256 amount,
        bytes memory data
    )
        private
    {
        if (to.isContract()) {
            try IERC1155Receiver(to).onERC1155Received(operator, from, id, amount, data) returns (bytes4 response) {
                if (response != IERC1155Receiver(to).onERC1155Received.selector) {
                    revert("ERC1155: ERC1155Receiver rejected tokens");
                }
            } catch Error(string memory reason) {
                revert(reason);
            } catch {
                revert("ERC1155: transfer to non ERC1155Receiver implementer");
            }
        }
    }

    function _doSafeBatchTransferAcceptanceCheck(
        address operator,
        address from,
        address to,
        uint256[] memory ids,
        uint256[] memory amounts,
        bytes memory data
    )
        private
    {
        if (to.isContract()) {
            try IERC1155Receiver(to).onERC1155BatchReceived(operator, from, ids, amounts, data) returns (bytes4 response) {
                if (response != IERC1155Receiver(to).onERC1155BatchReceived.selector) {
                    revert("ERC1155: ERC1155Receiver rejected tokens");
                }
            } catch Error(string memory reason) {
                revert(reason);
            } catch {
                revert("ERC1155: transfer to non ERC1155Receiver implementer");
            }
        }
    }

    function _asSingletonArray(uint256 element) private pure returns (uint256[] memory) {
        uint256[] memory array = new uint256[](1);
        array[0] = element;

        return array;
    }
}

// File: @openzeppelin/contracts/utils/Counters.sol



pragma solidity ^0.8.0;

/**
 * @title Counters
 * @author Matt Condon (@shrugs)
 * @dev Provides counters that can only be incremented or decremented by one. This can be used e.g. to track the number
 * of elements in a mapping, issuing ERC721 ids, or counting request ids.
 *
 * Include with `using Counters for Counters.Counter;`
 */
library Counters {
    struct Counter {
        // This variable should never be directly accessed by users of the library: interactions must be restricted to
        // the library's function. As of Solidity v0.5.2, this cannot be enforced, though there is a proposal to add
        // this feature: see https://github.com/ethereum/solidity/issues/4637
        uint256 _value; // default: 0
    }

    function current(Counter storage counter) internal view returns (uint256) {
        return counter._value;
    }

    function increment(Counter storage counter) internal {
        unchecked {
            counter._value += 1;
        }
    }

    function decrement(Counter storage counter) internal {
        uint256 value = counter._value;
        require(value > 0, "Counter: decrement overflow");
        unchecked {
            counter._value = value - 1;
        }
    }
}

contract MangoAccessControl{
    
    address payable public ceoAddress;
    address payable public cfoAddress;
    address payable public cooAddress;
    mapping(address => bool) public partnerAddress;
    
    modifier onlyCEO() {
        require(msg.sender == ceoAddress);
        _;
    }
    
     modifier onlyCFO() {
        require(msg.sender == cfoAddress);
        _;
    }
    
    modifier onlyCOO() {
        require(msg.sender == cooAddress);
        _;
    }
    
    modifier onlyPartner(){
        require(partnerAddress[msg.sender] == true);
        _;
    }
    
    function setPartnerAddress(address partener,bool isPartener) external onlyCEO{
        partnerAddress[partener] = isPartener;
    }
    
    
    function setCEO(address payable _newCEO) external onlyCEO {
        require(_newCEO != address(0));
        ceoAddress = _newCEO;
    }
    
    function setCFO(address payable _newCFO) external onlyCEO {
        require(_newCFO != address(0));

        cfoAddress = _newCFO;
    }
    
    function setCOO(address payable _newCOO) external onlyCEO {
        require(_newCOO != address(0));

        cooAddress = _newCOO;
    }
}

// File: contracts/MiniWar.sol

pragma solidity ^0.8.0;



contract MangoNFTBase is MangoAccessControl,ERC1155{
    
    string public constant name = "MangoDAO";
    string public constant symbol = "Mango";
    
    struct Game{
        address manager;
        string  name;
        uint256  gameId;
        uint16  version;
    }
    
    struct ItemAttr{
        string  name;
        uint16  gameId;
        uint16  itemType;
        bool    isSingle;
        bool    isCopyright;
        uint256 exp;
        uint256 parentMetaId;
        uint256 genes;
    }
    
    struct ItemShop{
        uint256 price;
        uint256 royalty;
        bool isOnline;
    }
    
    struct Auction {
        // tokenId
        uint256 tokenId;
        // Current owner of NFT
        address payable seller;
        
        uint16 amount;
        
        uint16 balanceAmount;
        // Price (in wei) at beginning of auction
        uint128 startingPrice;
        // Price (in wei) at end of auction
        uint128 endingPrice;
        // Duration (in seconds) of auction
        uint64 duration;
        // Time when auction started
        // NOTE: 0 if this auction has been concluded
        uint64 startedAt;
        bool isOver;
    }
    

    mapping (uint256 => Game)   public games;
    
    mapping (uint256 => ItemAttr) private tokenIdToItemAttr;
    
    mapping (uint256 => ItemShop) public tokenIdToItemShop;
    
    mapping (uint256 => Auction) public saleIdToAuction;

    using Counters for Counters.Counter;
    Counters.Counter public _tokenIds;
    Counters.Counter public _gameIds;

    mapping (uint256 => address) public creators;
    
    mapping (uint256 => uint256) public tokenSupply;
    
    mapping (uint256 => address) public copyrightPerson;
    
    uint256[] private shopItemIds;
    
    // Cut owner takes on each auction, measured in basis points (1/100 of a percent).
    // Values 0-10,000 map to 0%-100%
    uint256 public ownerCut;
    
    uint dnaDigits = 64;
    uint dnaModulus = 10 ** dnaDigits;

    event NFTCreate(address account, uint256 amount, uint16 itemType,string itemName,uint16 gameId,bool isSingle,bool isCopyright);
    event AuctionCreated(uint256 saleId,uint256 tokenId, uint16 amount,uint16 balance,uint256 startingPrice, uint256 endingPrice, uint256 duration);
    event AuctionSuccessful(uint256 saleId, uint256 amount,uint256 totalPrice, address winner);
    event AuctionCancelled(uint256 saleId);

    
    constructor() ERC1155("https://mangodao.com/api/item/{id}.json"){
        ceoAddress = payable(_msgSender());
        cfoAddress = payable(_msgSender());
        cooAddress = payable(_msgSender());
    }
    
    
    function setUrl(string memory newuri) public onlyCEO{
        _setURI(newuri);
    }
    
    function _generateRandomDna(uint256 _itemType) private view returns (uint256) {
        uint256 rand = uint256(keccak256(abi.encodePacked(_itemType,block.timestamp,block.number)));
        return rand % dnaModulus;
    }
    
    function _checkName(string memory str1, string memory str2) private pure returns(bool){
        return (keccak256(abi.encodePacked(str1)) == keccak256(abi.encodePacked(str2)));
    }
    
    
    function newGame(string memory gameName,uint16 version) public onlyPartner{
        uint256 newId = uint16(_gameIds.current());
        for(uint16 i = 0;i < newId; i++){
            Game memory beforGame = games[i];
            if(beforGame.manager == _msgSender() && _checkName(beforGame.name,gameName) == true){
                require(beforGame.version != version,"MangoDAOBase: The game version already exists");
            }else{
               require(_checkName(beforGame.name,gameName) == false,"MangoDAOBase: The game name already exists"); 
            }
        }
        Game memory game = Game(_msgSender(),gameName,newId,version);
        games[newId] = game;
        _gameIds.increment();
    }

    
    function createNFT(address account, uint256 amount, uint16 itemType,string memory itemName,uint16 gameId,bool isSingle,bool isCopyright,bytes memory data)public virtual onlyPartner{
        Game memory game = games[gameId];
        require(game.manager == _msgSender(),"MangoDAOBase: msgsender not manager!");
        
        uint256 newItemId = _tokenIds.current();
        if(isSingle == true || isCopyright == true){
            amount = 1;
        }
        if(isCopyright == true){
            copyrightPerson[newItemId] = _msgSender();
            isSingle = true;
        }
        _mint(account,newItemId,amount,data);
        tokenSupply[newItemId] = amount;
        uint256 genes = _generateRandomDna(itemType);
        ItemAttr memory attr = ItemAttr(itemName,gameId,itemType,isSingle,isCopyright,1,0,genes);
        tokenIdToItemAttr[newItemId] = attr;
        creators[newItemId] = _msgSender();
        _tokenIds.increment();
        NFTCreate(account,amount,itemType,itemName,gameId,isSingle,isCopyright);
    }
    
    function mint(address account, uint256 id, uint256 amount,bytes memory data)public onlyPartner{
        uint256 newItemId = _tokenIds.current();
        if(newItemId > id){
            require(creators[id] == _msgSender(),"ERC1155: caller is not minter of the token");
            ItemAttr memory attr = tokenIdToItemAttr[id];
            require(attr.isSingle == false,"ERC1155: this item isOnly");
            _mint(account,id,amount,data);
            tokenSupply[id] = tokenSupply[id] + amount;
        }
    }
    
    function levelUpItem(uint256 _tokenId1, uint256 _tokenId2) public returns(uint256 _rand,uint256 _genes){
        ItemAttr storage token1 = tokenIdToItemAttr[_tokenId1];
        ItemAttr storage token2 = tokenIdToItemAttr[_tokenId2];
        require(balanceOf(_msgSender(),_tokenId1) == 1 && balanceOf(msg.sender,_tokenId2) == 1,"You must have this item");
        require(token1.isCopyright == false && token2.isSingle == true,"Items cannot be upgraded");
        require(token1.itemType == token2.itemType && token1.parentMetaId == token2.parentMetaId,"Must be of the same type");

        uint256 newGenes = 0;
        uint256 randTime = block.timestamp % 2;
        uint256 divNum = 1 * 10 ** 62;
        uint256 tokenGenes1 = token1.genes;
        uint256 tokenGenes2 = token2.genes;
        for(uint i = 0;i < 32; i++){
            uint256 genes1 = tokenGenes1 / divNum;
            uint256 genes2 = tokenGenes2 / divNum;
            uint256 newNum = 0;
            if((randTime == genes1 % 2) || (randTime == genes2 % 2)){   //level up success
                newNum = genes1 > genes2 ? genes1:genes2;
            }else{                  //level up fail
                newNum = genes1 > genes2 ? genes2:genes1;
            }
            tokenGenes1 = tokenGenes1 - genes1 * divNum;
            tokenGenes2 = tokenGenes2 - genes2 * divNum;
            newGenes *= 100;
            newGenes += newNum;
            divNum /= 100;
        }
        _burn(_msgSender(),_tokenId1,1);
        _burn(_msgSender(),_tokenId2,1);
        
        uint256 newItemId = _tokenIds.current();
        _mint(_msgSender(),newItemId,1,"0x03");
        tokenSupply[newItemId] = 1;
        ItemAttr storage attr = tokenIdToItemAttr[_tokenId1];
        tokenIdToItemAttr[newItemId] = ItemAttr(attr.name,attr.gameId,attr.itemType,attr.isSingle,false,1,attr.parentMetaId,newGenes);
        creators[newItemId] = _msgSender();
        _tokenIds.increment();
        
        return (randTime,newGenes);
    }

    function getTokenIdInfo(uint256 _tokenId) public view returns(
        string memory _name,
        uint16 _gameId,
        uint16 _itemType,
        bool _isSingle,
        bool _isCopyright,
        uint256 _pID,
        uint256 _genes,
        uint256 _total
        ){
        ItemAttr storage itemAttr = tokenIdToItemAttr[_tokenId];
        uint256 total = tokenSupply[_tokenId];
        return (
            itemAttr.name,
            itemAttr.gameId,
            itemAttr.itemType,
            itemAttr.isSingle,
            itemAttr.isCopyright,
            itemAttr.parentMetaId,
            itemAttr.genes,
            total
            );
    }


    function getCreators(uint256 id) public view returns (address) {
        return creators[id];
    }
    
    function getUserItems(address user) public view returns(uint256[] memory ,uint256[] memory)
    {
        uint256 currentId = _tokenIds.current();
        uint256 count = 0;
        for(uint256 i = 0; i < currentId; i++){
            if(balanceOf(address(user),i)> 0){
                count++;
            }
        }
        uint256[] memory itemIds = new uint256[](count);
        uint256[] memory itemCount = new uint256[](count);
        uint256 index = 0;
        for(uint256 i = 0; i < currentId; i++){
            uint256 amount = balanceOf(address(user),i);
            if(amount > 0){
                itemIds[index] = i;
                itemCount[index] = amount;
                index++;
            }
        }
        return (itemIds,itemCount);
    }
    
    function itemShop(uint256 _tokenId) public payable{
        ItemAttr storage attr = tokenIdToItemAttr[_tokenId];
        require(attr.isCopyright == true,"Goods must have copyright attribute");
        
        ItemShop storage shop = tokenIdToItemShop[_tokenId];
        require(shop.isOnline == true,"Items are not online");
        require(msg.value >= shop.price,"be short of gold coins");
        
        address copyPer = copyrightPerson[_tokenId];
        require(copyPer != address(0), "ERC1155: copyPer to the zero address");
        
        uint256 newItemId = _tokenIds.current();
        _mint(msg.sender,newItemId,1,"0x02");
        tokenSupply[newItemId] = 1;
        uint256 genes = _generateRandomDna(attr.itemType);
        tokenIdToItemAttr[newItemId] = ItemAttr(attr.name,attr.gameId,attr.itemType,attr.isSingle,false,1,_tokenId,genes);
        creators[newItemId] = _msgSender();
        _tokenIds.increment();
        
        uint256 amount = msg.value;
        uint256 auctioneerCut = shop.price * shop.royalty / 10000;
        uint256 copyrightProceeds = shop.price - auctioneerCut;
        
        payable(copyPer).transfer(copyrightProceeds);
        
        uint256 bidExcess = amount - shop.price;

        payable(msg.sender).transfer(bidExcess);
    }
    
    function addShop(uint256 _tokenId,uint256 _price,uint256 _royalty) public onlyPartner{
        ItemAttr storage attr = tokenIdToItemAttr[_tokenId];
        Game memory game = games[attr.gameId];
        require(game.manager == _msgSender(),"MangoDAOBase: msgsender not manager!");
        require(attr.isCopyright == true,"Goods must have copyright attribute");
        require(_royalty <= 10000);
        ItemShop memory shop = ItemShop(_price,_royalty,true);
        tokenIdToItemShop[_tokenId] = shop;
        shopItemIds.push(_tokenId);
    }
    
    function updateShop(uint256 _tokenId,bool _Online) public onlyCEO{
        ItemShop storage shop = tokenIdToItemShop[_tokenId];
        shop.isOnline = _Online;
    }
    
    function getShopItemIds() public view returns(uint256[] memory){
        return shopItemIds;
    }
    
    
    function setCut(uint256 _cut)public onlyCEO{
        ownerCut = _cut;
    }

    /// @dev Escrows the NFT, assigning ownership to this contract.
    /// Throws if the escrow fails.
    /// @param _owner - Current owner address of token to escrow.
    /// @param _tokenId - ID of token whose approval to verify.
    function _escrow(address _owner, uint256 _tokenId,uint256 amount,bytes calldata data) internal {
        // it will throw if transfer fails
        safeTransferFrom(_owner, address(this), _tokenId,amount,data);
    }
    

    /// @dev Transfers an NFT owned by this contract to another address.
    /// Returns true if the transfer succeeds.
    /// @param _receiver - Address to transfer NFT to.
    /// @param _tokenId - ID of token to transfer.
    function _transfer(address _receiver, uint256 _tokenId,uint256 amount,bytes calldata data) internal {
        // it will throw if transfer fails
        _saleTransfer(address(this), _receiver, _tokenId,amount,data);
    }

    /// @dev Adds an auction to the list of open auctions. Also fires the
    ///  AuctionCreated event.
    /// @param _tokenId The ID of the token to be put on auction.
    /// @param _auction Auction to add.
    function _addAuction(uint256 _saleId,uint256 _tokenId, Auction memory _auction) internal {
        // Require that all auctions have a duration of
        // at least one minute. (Keeps our math from getting hairy!)
        require(_auction.duration >= 1 minutes);

        saleIdToAuction[_saleId] = _auction;

        AuctionCreated(
            uint256(_saleId),
            uint256(_tokenId),
            uint16(_auction.amount),
            uint16(_auction.balanceAmount),
            uint256(_auction.startingPrice),
            uint256(_auction.endingPrice),
            uint256(_auction.duration)
        );
    }

    /// @dev Cancels an auction unconditionally.
    function _cancelAuction(uint256 _saleId, uint256 tokenId,address _seller,uint16 balance,bytes calldata data) internal {
        _removeAuction(_saleId);
        _transfer(_seller, tokenId,balance,data);
        AuctionCancelled(_saleId);
    }

    /// @dev Computes the price and transfers winnings.
    /// Does NOT transfer ownership of token.
    function _bid(uint256 _saleId, uint256 _bidAmount,uint16 count)internal returns (uint256)
    {
        // Get a reference to the auction struct
        Auction storage auction = saleIdToAuction[_saleId];

        // Explicitly check that this auction is currently live.
        // (Because of how Ethereum mappings work, we can't just count
        // on the lookup above failing. An invalid _tokenId will just
        // return an auction object that is all zeros.)
        require(_isOnAuction(auction) && auction.isOver == false,"is on auction");
        
        require(auction.balanceAmount >= count,"understock");
        
        // Check that the bid is greater than or equal to the current price
        uint256 price = _currentPrice(auction) * count;
        require(_bidAmount >= price,"bidAmount must >= price");

        // Grab a reference to the seller before the auction struct
        // gets deleted.
        address payable seller = auction.seller;

        // The bid is good! Remove the auction before sending the fees
        // to the sender so we can't have a reentrancy attack.
        
        auction.balanceAmount = auction.balanceAmount - count;
        if(auction.balanceAmount <= 0){
            auction.isOver = true;
            ItemAttr storage attr = tokenIdToItemAttr[auction.tokenId];
            if(attr.isCopyright){
                copyrightPerson[auction.tokenId] = msg.sender;   
            }
        }

        // Transfer proceeds to seller (if there are any!)
        if (price > 0) {
            // Calculate the auctioneer's cut.
            // (NOTE: _computeCut() is guaranteed to return a
            // value <= price, so this subtraction can't go negative.)
            uint256 auctioneerCut = _computeCut(price);
            uint256 sellerProceeds = price - auctioneerCut;

            // NOTE: Doing a transfer() in the middle of a complex
            // method like this is generally discouraged because of
            // reentrancy attacks and DoS attacks if the seller is
            // a contract with an invalid fallback function. We explicitly
            // guard against reentrancy attacks by removing the auction
            // before calling transfer(), and the only thing the seller
            // can DoS is the sale of their own asset! (And if it's an
            // accident, they can call cancelAuction(). )
            seller.transfer(sellerProceeds);
        }

        // Calculate any excess funds included with the bid. If the excess
        // is anything worth worrying about, transfer it back to bidder.
        // NOTE: We checked above that the bid amount is greater than or
        // equal to the price so this cannot underflow.
        uint256 bidExcess = _bidAmount - price;

        // Return the funds. Similar to the previous transfer, this is
        // not susceptible to a re-entry attack because the auction is
        // removed before any transfers occur.
        
        payable(msg.sender).transfer(bidExcess);
        

        // Tell the world!
        AuctionSuccessful(_saleId, count,price, msg.sender);

        return price;
    }

    /// @dev Removes an auction from the list of open auctions.
    /// @param _saleId - ID of NFT on auction.
    function _removeAuction(uint256 _saleId) internal {
        delete saleIdToAuction[_saleId];
    }

    /// @dev Returns true if the NFT is on auction.
    /// @param _auction - Auction to check.
    function _isOnAuction(Auction storage _auction) internal view returns (bool) {
        return (_auction.startedAt > 0);
    }
    

    /// @dev Returns current price of an NFT on auction. Broken into two
    ///  functions (this one, that computes the duration from the auction
    ///  structure, and the other that does the price computation) so we
    ///  can easily test that the price computation works correctly.
    function _currentPrice(Auction storage _auction)
        internal
        view
        returns (uint256)
    {
        uint256 secondsPassed = 0;

        // A bit of insurance against negative values (or wraparound).
        // Probably not necessary (since Ethereum guarnatees that the
        // now variable doesn't ever go backwards).
        if (block.timestamp > _auction.startedAt) {
            secondsPassed = block.timestamp - _auction.startedAt;
        }

        return _computeCurrentPrice(
            _auction.startingPrice,
            _auction.endingPrice,
            _auction.duration,
            secondsPassed
        );
    }

    function _computeCurrentPrice(
        uint256 _startingPrice,
        uint256 _endingPrice,
        uint256 _duration,
        uint256 _secondsPassed
    )
        internal
        pure
        returns (uint256)
    {
        if (_secondsPassed >= _duration) {
            // We've reached the end of the dynamic pricing portion
            // of the auction, just return the end price.
            return _endingPrice;
        } else {
            // Starting price can be higher than ending price (and often is!), so
            // this delta can be negative.
            int256 totalPriceChange = int256(_endingPrice) - int256(_startingPrice);

            // This multiplication can't overflow, _secondsPassed will easily fit within
            // 64-bits, and totalPriceChange will easily fit within 128-bits, their product
            // will always fit within 256-bits.
            int256 currentPriceChange = totalPriceChange * int256(_secondsPassed) / int256(_duration);

            // currentPriceChange can be negative, but if so, will have a magnitude
            // less that _startingPrice. Thus, this result will always end up positive.
            int256 currentPrice = int256(_startingPrice) + currentPriceChange;

            return uint256(currentPrice);
        }
    }

    /// @dev Computes owner's cut of a sale.
    /// @param _price - Sale price of NFT.
    function _computeCut(uint256 _price) internal view returns (uint256) {
        // NOTE: We don't use SafeMath (or similar) in this function because
        //  all of our entry functions carefully cap the maximum values for
        //  currency (at 128-bits), and ownerCut <= 10000 (see the require()
        //  statement in the ClockAuction constructor). The result of this
        //  function is always guaranteed to be <= _price.
        return _price * ownerCut / 10000;
    }
    
    function updateCopyrightPerson(uint256 _tokenId) public{
        ItemAttr storage attr = tokenIdToItemAttr[_tokenId];
        require(attr.isCopyright == true,"MangoDAOBase:Item must have a copyright property");
        require(balanceOf(_msgSender(),_tokenId) > 0,"MangoDAOBase: The item is insufficient");
        copyrightPerson[_tokenId] = _msgSender();
    }

}


contract MangoNFT is MangoNFTBase {
    
    using Counters for Counters.Counter;
    Counters.Counter public _saleIds;

    constructor(uint256 _cut){
        require(_cut <= 10000);
        ownerCut = _cut;
    }

    function withdrawBalance() external onlyCFO{
        cfoAddress.transfer(address(this).balance);
    }

    function createAuction(
        uint256 _tokenId,
        uint256 _startingPrice,
        uint256 _endingPrice,
        uint256 _duration,
        uint16 amount,
        bytes calldata data
    )
        public
    {
       
        require(balanceOf(msg.sender,_tokenId) >= amount);
        _escrow(msg.sender, _tokenId,amount,data);
        uint256 saleId = _saleIds.current();
        Auction memory auction = Auction(
            _tokenId,
            payable(_msgSender()),
            uint16(amount),
            uint16(amount),
            uint128(_startingPrice),
            uint128(_endingPrice),
            uint64(_duration),
            uint64(block.timestamp),
            false
        );
        _addAuction(saleId,_tokenId, auction);
        _saleIds.increment();
    }

    /// @dev Bids on an open auction, completing the auction and transferring
    ///  ownership of the NFT if enough Ether is supplied.
    /// @param _saleId - ID of token to bid on.
    function bid(uint256 _saleId,uint16 amount,bytes calldata data)public payable
    {
        // _bid will throw if the bid or funds transfer fails
        require(amount > 0);
        Auction storage auction = saleIdToAuction[_saleId];
        uint256 _tokenId = auction.tokenId;
        _bid(_saleId, msg.value,amount);
        _transfer(msg.sender, _tokenId,amount,data);
    }
    
    function cancelAuction(uint256 _saleId,bytes calldata data)public
    {
        Auction storage auction = saleIdToAuction[_saleId];
        require(_isOnAuction(auction));
        address seller = auction.seller;
        uint256 tokenId = auction.tokenId;
        require(msg.sender == seller);
        _cancelAuction(_saleId, tokenId,seller,auction.balanceAmount,data);
    }
    
    function clearAuction(uint64 _beforTime,uint64 _afterTime,bool delOwner)public onlyCEO{
        uint256 saleId = _saleIds.current();
        for(uint256 i = 0;i < saleId;i++){
            Auction storage auction = saleIdToAuction[i];
            if(delOwner == false && auction.seller == ceoAddress){
                continue;
            }
            if(auction.startedAt > _beforTime && auction.startedAt < _afterTime){
                _removeAuction(i);
            }
        }
    }


    function getCurrentPrice(uint256 _saleId)
        external
        view
        returns (uint256)
    {
        Auction storage auction = saleIdToAuction[_saleId];
        require(_isOnAuction(auction));
        return _currentPrice(auction);
    }
    
    function getBalance() public view returns(uint256)
    {
        return address(this).balance;
    }

}
