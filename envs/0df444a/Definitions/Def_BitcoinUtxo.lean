-- Prove2me | Definitions.Def_BitcoinUtxo
-- name    : BitcoinUtxo
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-26T04:22:54.785878+00:00
-- url     : https://prove2.me/theorems/56b51545-fd03-440e-baf8-a3461b311412
-- title:
--   UTXO set, transaction checks, and block value accounting
-- statement:
--   Amounts are integers in satoshi, $\mathrm{COIN} = 10^{8}$, $\mathrm{MAX\_MONEY} = 2.1 \times 10^{15}$, and $\mathrm{moneyRange}(v) \iff 0 \le v \le \mathrm{MAX\_MONEY}$; $\mathrm{COINBASE\_MATURITY} = 100$. Transaction ids form an arbitrary type $T$ with decidable equality.
--
--   **Data.** An outpoint is a pair (txid, index). An output carries a value and an `unspendable` bit, standing for `scriptPubKey.IsUnspendable()`. A coin is an output with its creation height and coinbase flag. A transaction has a txid, input outpoints, outputs, and a coinbase flag standing for `IsCoinBase()`. The UTXO set is a list of (outpoint, coin) entries; `keysNodup` says the outpoints are pairwise distinct.
--
--   **View operations.** `getCoin` looks up an outpoint; `haveCoin` tests presence; `spendCoin` removes the entry; `addCoin` does nothing for an unspendable output and otherwise inserts the entry in place of any entry with the same outpoint; `addCoinsFrom` adds outputs $i, i+1, \dots$ of a transaction; `spendInputs` spends a list of outpoints; `updateCoins` spends the inputs (unless coinbase) and adds the outputs, as `UpdateCoins`.
--
--   **Values.** `sumValues` sums output values; `valueOut` is `GetValueOut()`; `valueIn` sums the values of the coins at a list of outpoints (zero for a missing coin); `totalValue` sums the values held in the set.
--
--   **Checks.** `outputsLoop` is the output loop of `CheckTransaction`: each value non-negative and at most `MAX_MONEY`, the running total in range. `checkTransaction` requires non-empty inputs and outputs, the output loop, and pairwise distinct inputs. `haveInputs` is `HaveInputs`. `inputsLoop` is the input loop of `CheckTxInputs`: each input present, a coinbase coin mature (spend height minus coin height at least 100), each value and the running `nValueIn` in range. `checkTxInputs` then requires $\mathrm{nValueIn} \ge \mathrm{valueOut}$ and returns the fee $\mathrm{nValueIn} - \mathrm{valueOut}$ if in range.
--
--   **Blocks.** `bip30Ok` is the BIP30 pre-check: no output of any transaction of the block already exists in the view. `checkBlockTxs` requires the first transaction to be a coinbase, the others not, all passing `checkTransaction`. `connectLoop` processes the transactions in order: a non-coinbase must pass `checkTxInputs`, its fee is added to `nFees` which must stay in range, then `updateCoins`. `connectBlock`$_s$ runs the structural check, the BIP30 check, the loop, and the coinbase bound $\mathrm{valueOut}(\text{coinbase}) \le \mathrm{nFees} + s(\text{height})$ for a subsidy function $s$. `connectChain`$_s$ connects a list of blocks at consecutive heights. `subsidySum`$_s(h, n) = \sum_{i<n} s(h+i)$.
--
--   These definitions fix the value-accounting semantics of block connection for the conservation theorems.
--
--   **Formalization Note.** Heights are `Nat` and the maturity test uses truncated subtraction, which rejects a spend below the coin's height as the signed source does. `fEnforceBIP30` is fixed to enforced. Size, script-length, null-prevout and script-validity rules are not modeled. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CheckTransaction, src/consensus/tx_check.cpp lines 11-68: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp; Consensus::CheckTxInputs, src/consensus/tx_verify.cpp (lines 157-220): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp; CCoinsViewCache::AddCoin, AddCoins, SpendCoin, HaveInputs, src/coins.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp; UpdateCoins, BIP30 check (lines 2396-2475), fee accumulation and coinbase bound in Chainstate::ConnectBlock (lines 2518-2612), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; COIN, MAX_MONEY, MoneyRange, src/consensus/amount.h; COINBASE_MATURITY, src/consensus/consensus.h

import Std

namespace BitcoinUtxo

/-! Transcription of the value-accounting rules of Bitcoin Core at revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`: `CheckTransaction` (`consensus/tx_check.cpp`),
`Consensus::CheckTxInputs` (`consensus/tx_verify.cpp`), `CCoinsViewCache::AddCoin` / `SpendCoin`,
`AddCoins`, `HaveInputs` (`coins.cpp`), `UpdateCoins`, the BIP30 pre-check and the fee / coinbase
accounting of `Chainstate::ConnectBlock` (`validation.cpp`), with `COIN`, `MAX_MONEY`, `MoneyRange`
(`consensus/amount.h`) and `COINBASE_MATURITY` (`consensus/consensus.h`).

Transaction ids are an arbitrary type `T` with decidable equality. Amounts are `Int`, as `CAmount`
is a signed 64-bit integer whose sign the checks test explicitly. Scripts are abstracted to the one
bit the accounting reads: whether an output's `scriptPubKey.IsUnspendable()`, in which case
`AddCoin` does not add it to the UTXO set. The UTXO set is a list of `(outpoint, coin)` entries
with pairwise distinct outpoints, standing for the map `cacheCoins`. -/

variable {T : Type} [DecidableEq T]

/-- `consensus/amount.h`: `COIN{100'000'000}`. -/
def COIN : Int := 100000000

/-- `consensus/amount.h`: `MAX_MONEY{21'000'000 * COIN}`. -/
def MAX_MONEY : Int := 21000000 * COIN

/-- `consensus/amount.h`: `MoneyRange(nValue) = (nValue >= 0 && nValue <= MAX_MONEY)`. -/
def moneyRange (v : Int) : Bool := decide (0 ≤ v ∧ v ≤ MAX_MONEY)

/-- `consensus/consensus.h`: `COINBASE_MATURITY = 100`. -/
def COINBASE_MATURITY : Nat := 100

/-- `COutPoint`: a transaction id and an output index. -/
structure OutPoint (T : Type) where
  txid : T
  n : Nat
  deriving DecidableEq

/-- `CTxOut`, reduced to its value and to `scriptPubKey.IsUnspendable()`. -/
structure TxOut where
  value : Int
  unspendable : Bool
  deriving DecidableEq

/-- `Coin`: an unspent output with its creation height and coinbase flag. -/
structure Coin where
  out : TxOut
  height : Nat
  isCoinbase : Bool
  deriving DecidableEq

/-- `CTransaction`, reduced to what the accounting reads. `isCoinbase` stands for
`IsCoinBase()`, i.e. a single null previous outpoint, which `CheckBlock` requires of the first
transaction of a block and forbids for the others. -/
structure Tx (T : Type) where
  txid : T
  vin : List (OutPoint T)
  vout : List TxOut
  isCoinbase : Bool

/-- The UTXO set: `(outpoint, coin)` entries, meant to have pairwise distinct outpoints. -/
abbrev UtxoSet (T : Type) := List (OutPoint T × Coin)

/-- The entry for an outpoint, if present. -/
def getCoin : UtxoSet T → OutPoint T → Option Coin
  | [], _ => none
  | (k, c) :: rest, op => if k = op then some c else getCoin rest op

/-- `HaveCoin`. -/
def haveCoin (u : UtxoSet T) (op : OutPoint T) : Bool := (getCoin u op).isSome

/-- The outpoints are pairwise distinct. -/
def keysNodup (u : UtxoSet T) : Prop := (u.map Prod.fst).Nodup

/-- `SpendCoin`: remove the entry for the outpoint. -/
def spendCoin : UtxoSet T → OutPoint T → UtxoSet T
  | [], _ => []
  | (k, c) :: rest, op => if k = op then spendCoin rest op else (k, c) :: spendCoin rest op

/-- `AddCoin`: an unspendable output is not added; otherwise the entry replaces any entry with the
same outpoint (`possible_overwrite`); the BIP30 check of `ConnectBlock` is what rules out a live
entry being overwritten. -/
def addCoin (u : UtxoSet T) (op : OutPoint T) (c : Coin) : UtxoSet T :=
  if c.out.unspendable then u else (op, c) :: spendCoin u op

/-- `AddCoins`: add the outputs `vout[i]` at outpoints `(txid, i)`, starting from index `i`. -/
def addCoinsFrom (txid : T) (height : Nat) (cb : Bool) : UtxoSet T → Nat → List TxOut → UtxoSet T
  | u, _, [] => u
  | u, i, o :: rest => addCoinsFrom txid height cb (addCoin u ⟨txid, i⟩ ⟨o, height, cb⟩) (i + 1) rest

/-- `SpendCoin` on every input. -/
def spendInputs : UtxoSet T → List (OutPoint T) → UtxoSet T
  | u, [] => u
  | u, op :: rest => spendInputs (spendCoin u op) rest

/-- `UpdateCoins`: mark the inputs spent (not for a coinbase), then add the outputs. -/
def updateCoins (u : UtxoSet T) (tx : Tx T) (height : Nat) : UtxoSet T :=
  addCoinsFrom tx.txid height tx.isCoinbase (if tx.isCoinbase then u else spendInputs u tx.vin) 0 tx.vout

/-- The output-value loop of `CheckTransaction`: each value non-negative, at most `MAX_MONEY`, and
the running total in range; returns the total. -/
def outputsLoop : List TxOut → Int → Option Int
  | [], acc => some acc
  | o :: rest, acc =>
    if o.value < 0 then none
    else if MAX_MONEY < o.value then none
    else if !moneyRange (acc + o.value) then none
    else outputsLoop rest (acc + o.value)

/-- The sum of a list of output values. -/
def sumValues : List TxOut → Int
  | [] => 0
  | o :: rest => o.value + sumValues rest

/-- `CTransaction::GetValueOut()`: the sum of the output values. -/
def valueOut (tx : Tx T) : Int := sumValues tx.vout

/-- `nValueIn`: the sum of the values of the coins at the given outpoints (zero for a missing coin). -/
def valueIn (u : UtxoSet T) : List (OutPoint T) → Int
  | [] => 0
  | op :: rest => (match getCoin u op with | none => 0 | some c => c.out.value) + valueIn u rest

/-- `CheckTransaction`, restricted to the context-free rules that concern values and inputs:
non-empty inputs and outputs, the output-value loop, and no duplicate inputs (CVE-2018-17144).
The serialized-size bound, the coinbase script-length bound and the null-prevout test concern
serialization and scripts and are outside this file. -/
def checkTransaction (tx : Tx T) : Bool :=
  !tx.vin.isEmpty && !tx.vout.isEmpty && (outputsLoop tx.vout 0).isSome &&
    decide (tx.vin.Nodup)

/-- `HaveInputs`. -/
def haveInputs (u : UtxoSet T) (tx : Tx T) : Bool :=
  tx.isCoinbase || tx.vin.all fun op => haveCoin u op

/-- The input loop of `CheckTxInputs`: for each input, the coin must exist, a coinbase coin must
be mature (`nSpendHeight - coin.nHeight >= COINBASE_MATURITY`), and the coin value and the running
total must be in `MoneyRange`; returns `nValueIn`. -/
def inputsLoop (u : UtxoSet T) (spendHeight : Nat) : List (OutPoint T) → Int → Option Int
  | [], acc => some acc
  | op :: rest, acc =>
    match getCoin u op with
    | none => none
    | some coin =>
      if coin.isCoinbase && decide (spendHeight - coin.height < COINBASE_MATURITY) then none
      else
        let acc' := acc + coin.out.value
        if !moneyRange coin.out.value || !moneyRange acc' then none
        else inputsLoop u spendHeight rest acc'

/-- `Consensus::CheckTxInputs`: returns the fee `txfee` on success. -/
def checkTxInputs (u : UtxoSet T) (tx : Tx T) (spendHeight : Nat) : Option Int :=
  if !haveInputs u tx then none
  else
    match inputsLoop u spendHeight tx.vin 0 with
    | none => none
    | some valueIn =>
      let vOut := valueOut tx
      if valueIn < vOut then none
      else
        let fee := valueIn - vOut
        if !moneyRange fee then none else some fee

/-- The BIP30 pre-check of `ConnectBlock`: no output of any transaction of the block may already
exist as an unspent coin. -/
def bip30Ok (u : UtxoSet T) (block : List (Tx T)) : Bool :=
  block.all fun tx => (List.range tx.vout.length).all fun o => !haveCoin u ⟨tx.txid, o⟩

/-- The structural requirements `CheckBlock` places on the transactions: every transaction passes
`CheckTransaction`, the first is a coinbase and no other is. -/
def checkBlockTxs : List (Tx T) → Bool
  | [] => false
  | cb :: rest => cb.isCoinbase && checkTransaction cb && rest.all fun tx => !tx.isCoinbase && checkTransaction tx

/-- The per-transaction loop of `ConnectBlock`, restricted to accounting: for a non-coinbase
transaction, `CheckTxInputs` must succeed and the accumulated fees must stay in `MoneyRange`;
then `UpdateCoins`. Returns the final view and `nFees`. -/
def connectLoop (height : Nat) : UtxoSet T → Int → List (Tx T) → Option (UtxoSet T × Int)
  | u, fees, [] => some (u, fees)
  | u, fees, tx :: rest =>
    if tx.isCoinbase then connectLoop height (updateCoins u tx height) fees rest
    else
      match checkTxInputs u tx height with
      | none => none
      | some fee =>
        let fees' := fees + fee
        if !moneyRange fees' then none
        else connectLoop height (updateCoins u tx height) fees' rest

/-- `ConnectBlock`, restricted to value accounting, at a height where BIP30 is enforced: the
structural checks, the BIP30 pre-check, the transaction loop, and the coinbase bound
`GetValueOut() <= nFees + GetBlockSubsidy(height)`. The subsidy function is a parameter. -/
def connectBlock (subsidy : Nat → Int) (u : UtxoSet T) (height : Nat) (block : List (Tx T)) :
    Option (UtxoSet T × Int) :=
  if !checkBlockTxs block then none
  else if !bip30Ok u block then none
  else
    match connectLoop height u 0 block with
    | none => none
    | some (u', fees) =>
      match block with
      | [] => none
      | cb :: _ => if valueOut cb > fees + subsidy height then none else some (u', fees)

/-- Connect a sequence of blocks at consecutive heights starting from `height`. -/
def connectChain (subsidy : Nat → Int) : UtxoSet T → Nat → List (List (Tx T)) → Option (UtxoSet T)
  | u, _, [] => some u
  | u, height, block :: rest =>
    match connectBlock subsidy u height block with
    | none => none
    | some (u', _) => connectChain subsidy u' (height + 1) rest

/-- The total value held in the UTXO set. -/
def totalValue : UtxoSet T → Int
  | [] => 0
  | (_, c) :: rest => c.out.value + totalValue rest

/-- The sum of the subsidies at heights `h, h + 1, …, h + n - 1`. -/
def subsidySum (subsidy : Nat → Int) (h : Nat) : Nat → Int
  | 0 => 0
  | n + 1 => subsidySum subsidy h n + subsidy (h + n)

end BitcoinUtxo


