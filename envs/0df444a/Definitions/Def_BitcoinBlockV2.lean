-- Prove2me | Definitions.Def_BitcoinBlockV2
-- name    : BitcoinBlockV2
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-28T14:58:31.352031+00:00
-- url     : https://prove2.me/theorems/611301b7-b5cc-46e0-9f81-18fee0222b41
-- title:
--   Block validation composed (revision 2): header path, CheckBlock, ContextualCheckBlock, ConnectBlock, DisconnectBlock, and the declarative specification
-- statement:
--   **Constants.** `MAX_BLOCK_WEIGHT` = 4,000,000, `MAX_BLOCK_SIGOPS_COST` = 80,000, `WITNESS_SCALE_FACTOR` = 4, `LOCKTIME_THRESHOLD` = 500,000,000, `SEQUENCE_FINAL` = 0xffffffff, `MINIMUM_WITNESS_COMMITMENT` = 38, `BIP34_IMPLIES_BIP30_LIMIT` = 1,983,702, `MAX_FUTURE_BLOCK_TIME` = 7200 s, `COINBASE_MATURITY` = 100, `MAX_MONEY`; the mainnet hashes `BIP34Hash`, the two `script_flag_exceptions`, the two `IsBIP30Repeat` blocks (91842, 91880) and the two `IsBIP30Unspendable` blocks (91722, 91812), in serialized byte order.
--
--   **Transactions.** `isCoinBase` (one input with a null prevout), `isUnspendable` (`OP_RETURN` first or over 10,000 bytes), `valueOut`, `checkTransaction` (`CheckTransaction`: non-empty inputs and outputs, witness-stripped size within the weight limit, each output and the running total in `MoneyRange`, no duplicate prevouts, coinbase script 2–100 bytes, no null prevout otherwise), `isFinalTx`.
--
--   **Signature operations.** `getSigOpCount accurate` is `CScript::GetSigOpCount(fAccurate)`; `p2shSigOpCount` is the redeem-script count; `witnessSigOps`/`countWitnessSigOps` are `CountWitnessSigOps`; `legacySigOpCount` and `txSigOpCost` are `GetLegacySigOpCount` and `GetTransactionSigOpCost` (legacy and P2SH counts weighted by 4, witness counts unweighted; P2SH only with the flag).
--
--   **Ledger.** `Coin` (output, height, coinbase flag); a `Ledger` is an association list; `getCoin`, `haveCoin`, `accessCoin`, `spendCoin`, `addCoin` (unspendable outputs are not stored; an existing entry is replaced), `updateCoins` (`UpdateCoins`), `txUndo` (the coins an input list spends), `Equiv` (same coins), `keysNodup`, `LedgerOk`.
--
--   **Per-transaction checks.** `checkTxInputs` (`Consensus::CheckTxInputs`, returning the fee), `sequenceLocksOk` (`SequenceLocks` through the BIP68 mission), `inputScriptsOk` (`CheckInputScripts` through the complete `VerifyScript` with the Taproot branch and the spent outputs), and `connectLoop`, the transaction loop of `ConnectBlock` in source order (inputs, fee range, BIP68, sigop budget, scripts, `UpdateCoins`), accumulating the ledger, fees, sigop cost and undo data.
--
--   **Chain state.** `ChainState` is the list of validated headers from the genesis and the ledger; `initialState`; tip, heights, `timesTo`/`mtpAt`/`mtp` (`GetMedianTimePast` through the Header mission), `requiredBits` (`GetNextWorkRequired` through the PoW mission with the period's first block), `blockProof`/`chainWork` (`GetBlockProof`, `nChainWork`), `hashValue`.
--
--   **The validation path.** `checkBlock` (`CheckBlock` with proof of work and merkle root through the Merkle mission), `heightScript`/`witnessCommitmentIndex`/`checkWitnessMalleation`/`contextualCheckBlock` (`ContextualCheckBlock`), `bip30Checked` (`fEnforceBIP30 || nHeight >= BIP34_IMPLIES_BIP30_LIMIT`), `bip30Ok`, `connectBlock` (`ConnectBlock` after `CheckBlock`: genesis shortcut, BIP30, flags from the Activation mission, the loop, the coinbase bound with `GetBlockSubsidy`), `acceptHeader` (`AcceptBlockHeader` on the tip, in source order), and `validate S B t : Outcome` — the source-linked outcome $C(S,B,t)$ with constructors `accept S' undo`, `invalid`, `futureTime` (`BLOCK_TIME_FUTURE`) and `missingPrev`. `accepts`, and `Reachable` (from the genesis state through accepted blocks).
--
--   **Disconnect.** `applyTxInUndo`, `restoreInputs`, `spendOutputs`, `disconnectTx`, `disconnectTxs`, `disconnectBlock` (`DisconnectBlock` with the clean flag and the two exception blocks).
--
--   **Specification.** `TxSpec`, `valueIn`, `feeOf`, `TxInputsSpec` (existing mature coins, value bounds, the BIP68 *specification* `satisfiesBIP68`, every input script), `TxsSpec` (transactions applied in order), `applyTxs`, `totalFees`, `applySpec` ($\mathrm{ApplySpec}(S,B)$), `HeaderSpec` (the PoW mission's `specTarget` form, parent, difficulty, median-time floor, clock ceiling, version floors), `BlockSpec`, `ContextSpec`, `LedgerSpec` (BIP30 where it applies, the sequence, the coinbase bound with `specSubsidy`), `Valid` ($V(S,B,t)$), `LedgerOk`, `WellFormed`.
--
--   **Revision 2.** Supersedes the first publication of this definition: `p2shSigOpCount` is now the per-input term of `GetP2SHSigOpCount` (zero unless the spent output is P2SH); the first version also added the accurate count of every non-P2SH spent script, overcounting a P2PKH spend as 8 instead of 4 (stricter than Core, never more lenient). Found by the source review in the repository's `REVIEW_SPOT11.md`; nothing else changed and every theorem statement is identical.
--
--   **Formalization Note.** `fJustCheck` is false and script checks are always performed (no assumed-valid shortcut); the chain is linear (a header not on the tip is `missingPrev`, the orphan case); flags, subsidy, difficulty, median time, merkle root and scripts are the published missions' functions. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Std
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinActivation
import Definitions.Def_BitcoinHeader
import Definitions.Def_BitcoinPow
import Definitions.Def_BitcoinSubsidy
import Definitions.Def_BitcoinMerkle
import Definitions.Def_BIP68_Core
import Definitions.Def_BitcoinUtxo

namespace BitcoinBlockV2

/-! Composition of Bitcoin Core's block validation at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`,
mainnet parameters: the header path of `AcceptBlockHeader` (`CheckBlockHeader`, the previous-block
lookup, `ContextualCheckBlockHeader`), `CheckBlock`, `ContextualCheckBlock` (`IsFinalTx`, the BIP34
coinbase height, `CheckWitnessMalleation`, `GetBlockWeight`), and `ConnectBlock` (the BIP30 rule with
`IsBIP30Repeat` and the BIP34 shortcut, `CheckTxInputs`, `SequenceLocks`, `GetTransactionSigOpCost`,
`CheckInputScripts` through the complete `VerifyScript`, `UpdateCoins`, the coinbase bound), together
with `DisconnectBlock`/`ApplyTxInUndo`, the genesis state, `GetBlockProof`, and a declarative
specification of block admissibility and of the ledger transition. -/

open BitcoinSer (Byte Bytes Tx TxIn TxOut OutPoint Header Block)

/-! ### Constants (`consensus/consensus.h`, `script/script.h`, `validation.cpp`, `chainparams.cpp`) -/

def MAX_BLOCK_WEIGHT : Nat := 4000000
def MAX_BLOCK_SIGOPS_COST : Nat := 80000
def WITNESS_SCALE_FACTOR : Nat := 4
def LOCKTIME_THRESHOLD : Nat := 500000000
def SEQUENCE_FINAL : Nat := 0xffffffff
def MINIMUM_WITNESS_COMMITMENT : Nat := 38
def BIP34_IMPLIES_BIP30_LIMIT : Nat := 1983702
def MAX_FUTURE_BLOCK_TIME : Int := 2 * 60 * 60
def COINBASE_MATURITY : Nat := 100
def MAX_MONEY : Int := 2100000000000000

/-- `MoneyRange`. -/
def moneyRange (v : Int) : Bool := decide (0 ≤ v ∧ v ≤ MAX_MONEY)

/-- Block hashes in serialized (internal) byte order: `consensus.BIP34Hash`. -/
def bip34Hash : Bytes := [0xb8, 0x08, 0x08, 0x9c, 0x75, 0x6a, 0xdd, 0x15, 0x91, 0xb1, 0xd1, 0x7b, 0xab, 0x44, 0xbb, 0xa3, 0xfe, 0xd9, 0xe0, 0x2f, 0x94, 0x2a, 0xb4, 0x89, 0x4b, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
/-- The `script_flag_exceptions` keys. -/
def bip16ExceptionHash : Bytes := [0x22, 0x9c, 0x4f, 0xac, 0x88, 0xba, 0xb1, 0x94, 0xeb, 0x08, 0xf1, 0xa5, 0x28, 0xcc, 0x30, 0x8d, 0xed, 0x23, 0x97, 0xf4, 0xf4, 0xeb, 0x6e, 0x75, 0xdc, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
def taprootExceptionHash : Bytes := [0xad, 0x95, 0xe3, 0xa1, 0x5e, 0xe5, 0xff, 0xd5, 0x85, 0xc5, 0xe8, 0x1d, 0x44, 0xb5, 0x6a, 0x98, 0x1e, 0x84, 0x2d, 0x5b, 0xc3, 0x14, 0x0f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
/-- `IsBIP30Repeat`: the two blocks whose coinbases repeat earlier ones. -/
def bip30Repeat91842 : Bytes := [0xec, 0xca, 0xe0, 0x00, 0xe3, 0xc8, 0xe4, 0xe0, 0x93, 0x93, 0x63, 0x60, 0x43, 0x1f, 0x3b, 0x76, 0x03, 0xc5, 0x63, 0xc1, 0xff, 0x61, 0x81, 0x39, 0x0a, 0x4d, 0x0a, 0x00, 0x00, 0x00, 0x00, 0x00]
def bip30Repeat91880 : Bytes := [0x21, 0xd7, 0x7c, 0xcb, 0x4c, 0x08, 0x38, 0x6a, 0x04, 0xac, 0x01, 0x96, 0xae, 0x10, 0xf6, 0xa1, 0xd2, 0xc2, 0xa3, 0x77, 0x55, 0x8c, 0xa1, 0x90, 0xf1, 0x43, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00]
/-- `IsBIP30Unspendable`: the two blocks whose coinbases were overwritten. -/
def bip30Unspendable91722 : Bytes := [0x8e, 0xd0, 0x4d, 0x57, 0xf2, 0xf3, 0xcd, 0xc6, 0xa6, 0xe5, 0x55, 0x69, 0xdc, 0x16, 0x54, 0xe1, 0xf2, 0x19, 0x84, 0x7f, 0x66, 0xe7, 0x26, 0xdc, 0xa2, 0x71, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00]
def bip30Unspendable91812 : Bytes := [0x2f, 0x6f, 0x30, 0xf9, 0xd6, 0x83, 0xde, 0xb8, 0x5d, 0x93, 0x14, 0xef, 0x5d, 0xcf, 0x36, 0xaf, 0x66, 0xd9, 0xe3, 0xce, 0x1a, 0x2b, 0x79, 0xd4, 0xae, 0xf0, 0x0a, 0x00, 0x00, 0x00, 0x00, 0x00]

def isBIP30Repeat (height : Nat) (hash : Bytes) : Bool :=
  (decide (height = 91842) && decide (hash = bip30Repeat91842)) ||
  (decide (height = 91880) && decide (hash = bip30Repeat91880))

def isBIP30Unspendable (height : Nat) (hash : Bytes) : Bool :=
  (decide (height = 91722) && decide (hash = bip30Unspendable91722)) ||
  (decide (height = 91812) && decide (hash = bip30Unspendable91812))

/-- The `script_flag_exceptions` lookup by block hash. -/
def scriptException (hash : Bytes) : BitcoinActivation.ScriptException :=
  if hash = bip16ExceptionHash then .bip16Block
  else if hash = taprootExceptionHash then .taprootBlock
  else .none

/-! ### Transactions (`primitives/transaction.h`, `consensus/tx_check.cpp`, `tx_verify.cpp`) -/

/-- `COutPoint::IsNull`. -/
def outPointNull (o : OutPoint) : Bool := decide (o.hash = List.replicate 32 0) && decide (o.n = 0xffffffff)

/-- `CTransaction::IsCoinBase`: one input whose prevout is null. -/
def isCoinBase (tx : Tx) : Bool :=
  match tx.vin with
  | [i] => outPointNull i.prevout
  | _ => false

/-- `CScript::IsUnspendable`: starts with `OP_RETURN`, or longer than `MAX_SCRIPT_SIZE`. -/
def isUnspendable (s : Bytes) : Bool :=
  (decide (0 < s.length) && decide ((s.getD 0 0) = BitcoinScript.OP_RETURN)) ||
  decide (BitcoinVerify.MAX_SCRIPT_SIZE < s.length)

def sumValues : List TxOut → Int
  | [] => 0
  | o :: rest => o.nValue + sumValues rest

/-- `CTransaction::GetValueOut`. -/
def valueOut (tx : Tx) : Int := sumValues tx.vout

/-- The output loop of `CheckTransaction`: each value in `[0, MAX_MONEY]` and the running total in
`MoneyRange`. -/
def outputsLoop : List TxOut → Int → Option Int
  | [], acc => some acc
  | o :: rest, acc =>
    if o.nValue < 0 then none
    else if MAX_MONEY < o.nValue then none
    else if !moneyRange (acc + o.nValue) then none
    else outputsLoop rest (acc + o.nValue)

/-- `CheckTransaction`. -/
def checkTransaction (tx : Tx) : Bool :=
  !tx.vin.isEmpty && !tx.vout.isEmpty &&
  decide ((BitcoinSer.serTx false tx).length * WITNESS_SCALE_FACTOR ≤ MAX_BLOCK_WEIGHT) &&
  (outputsLoop tx.vout 0).isSome &&
  decide ((tx.vin.map TxIn.prevout).Nodup) &&
  (if isCoinBase tx then
     decide (2 ≤ (tx.vin.headD ⟨⟨[], 0⟩, [], 0, []⟩).scriptSig.length ∧
             (tx.vin.headD ⟨⟨[], 0⟩, [], 0, []⟩).scriptSig.length ≤ 100)
   else tx.vin.all fun i => !outPointNull i.prevout)

/-- `IsFinalTx(tx, nBlockHeight, nBlockTime)`. -/
def isFinalTx (tx : Tx) (height : Nat) (blockTime : Int) : Bool :=
  if tx.nLockTime = 0 then true
  else if (tx.nLockTime : Int) < (if tx.nLockTime < LOCKTIME_THRESHOLD then (height : Int) else blockTime) then true
  else tx.vin.all fun i => decide (i.nSequence = SEQUENCE_FINAL)

/-! ### Signature-operation counting (`script/script.cpp`, `script/interpreter.cpp`, `tx_verify.cpp`) -/

/-- `CScript::GetSigOpCount(fAccurate)`: `CHECKSIG(VERIFY)` counts one, `CHECKMULTISIG(VERIFY)` counts
the preceding `OP_n` when accurate, else 20; a parse failure ends the count. `last` is the previous
opcode (`OP_INVALIDOPCODE` initially). -/
def sigOpCountAux (accurate : Bool) : Nat → Bytes → Nat → Nat → Nat
  | _, [], _, n => n
  | 0, _, _, n => n
  | fuel + 1, s, last, n =>
    match BitcoinSig.getOp s with
    | none => n
    | some (.push _, r) => sigOpCountAux accurate fuel r 0 n
    | some (.op c, r) =>
      let n' :=
        if c = BitcoinScript.OP_CHECKSIG ∨ c = BitcoinScript.OP_CHECKSIGVERIFY then n + 1
        else if c = BitcoinScript.OP_CHECKMULTISIG ∨ c = BitcoinScript.OP_CHECKMULTISIGVERIFY then
          if accurate ∧ 0x51 ≤ last ∧ last ≤ 0x60 then n + BitcoinVerify.decodeOpN last
          else n + BitcoinScript.MAX_PUBKEYS_PER_MULTISIG
        else n
      sigOpCountAux accurate fuel r c.toNat n'

def getSigOpCount (accurate : Bool) (s : Bytes) : Nat := sigOpCountAux accurate s.length s 0xff 0

/-- The last datum pushed by a push-only script (`vData` after the `GetOp` loop); `none` when some
instruction fails to parse or is above `OP_16`. -/
def lastPushAux : Nat → Bytes → Bytes → Option Bytes
  | _, [], d => some d
  | 0, _, _ => none
  | fuel + 1, s, _ =>
    match BitcoinSig.getOp s with
    | none => none
    | some (.push d, r) => lastPushAux fuel r d
    | some (.op c, r) => if BitcoinScript.OP_16 < c then none else lastPushAux fuel r []

def lastPush (s : Bytes) : Option Bytes := lastPushAux s.length s []

/-- The per-input term of `GetP2SHSigOpCount`: `0` unless the spent output is P2SH, in which case
`CScript::GetSigOpCount(scriptSig)` on it, the accurate count of the redeem script (the last push of
`scriptSig`), or `0` when `scriptSig` is not push-only. -/
def p2shSigOpCount (scriptPubKey scriptSig : Bytes) : Nat :=
  if !BitcoinVerify.isPayToScriptHash scriptPubKey then 0
  else match lastPush scriptSig with
    | none => 0
    | some d => getSigOpCount true d

/-- `WitnessSigOps`. -/
def witnessSigOps (version : Nat) (program : Bytes) (witness : List Bytes) : Nat :=
  if version = 0 then
    if program.length = 20 then 1
    else if program.length = 32 ∧ 0 < witness.length then getSigOpCount true (witness.getLast?.getD [])
    else 0
  else 0

/-- `CountWitnessSigOps(scriptSig, scriptPubKey, witness, flags)`. -/
def countWitnessSigOps (f : BitcoinActivation.ScriptFlags) (scriptSig scriptPubKey : Bytes) (witness : List Bytes) : Nat :=
  if !f.witness then 0
  else match BitcoinVerify.isWitnessProgram scriptPubKey with
    | some (v, p) => witnessSigOps v p witness
    | none =>
      if BitcoinVerify.isPayToScriptHash scriptPubKey && BitcoinVerify.isPushOnly scriptSig then
        match lastPush scriptSig with
        | none => 0
        | some d =>
          match BitcoinVerify.isWitnessProgram d with
          | some (v, p) => witnessSigOps v p witness
          | none => 0
      else 0

/-- `GetLegacySigOpCount`. -/
def legacySigOpCount (tx : Tx) : Nat :=
  (tx.vin.map fun i => getSigOpCount false i.scriptSig).sum +
  (tx.vout.map fun o => getSigOpCount false o.scriptPubKey).sum

/-! ### The ledger (`coins.h`, `coins.cpp`, `validation.cpp`) -/

/-- `Coin`: an unspent output with its creation height and coinbase flag. -/
structure Coin where
  out : TxOut
  height : Nat
  isCoinbase : Bool
  deriving DecidableEq, Repr

def dummyCoin : Coin := ⟨⟨-1, []⟩, 0, false⟩

/-- The UTXO set as an association list keyed by outpoint. -/
abbrev Ledger := List (OutPoint × Coin)

def getCoin : Ledger → OutPoint → Option Coin
  | [], _ => none
  | (k, c) :: rest, op => if k = op then some c else getCoin rest op

def haveCoin (u : Ledger) (op : OutPoint) : Bool := (getCoin u op).isSome

/-- `AccessCoin`: the coin, or a spent (dummy) coin. -/
def accessCoin (u : Ledger) (op : OutPoint) : Coin := (getCoin u op).getD dummyCoin

def spendCoin : Ledger → OutPoint → Ledger
  | [], _ => []
  | (k, c) :: rest, op => if k = op then spendCoin rest op else (k, c) :: spendCoin rest op

/-- `AddCoin`: unspendable outputs are not stored; otherwise the entry replaces any existing one. -/
def addCoin (u : Ledger) (op : OutPoint) (c : Coin) : Ledger :=
  if isUnspendable c.out.scriptPubKey then u else (op, c) :: spendCoin u op

def addCoinsFrom (txid : Bytes) (height : Nat) (cb : Bool) : Ledger → Nat → List TxOut → Ledger
  | u, _, [] => u
  | u, i, o :: rest => addCoinsFrom txid height cb (addCoin u ⟨txid, i⟩ ⟨o, height, cb⟩) (i + 1) rest

def spendInputs : Ledger → List TxIn → Ledger
  | u, [] => u
  | u, i :: rest => spendInputs (spendCoin u i.prevout) rest

/-- `UpdateCoins(tx, view, undo, height)`: spend the inputs of a non-coinbase, then `AddCoins`. -/
def updateCoins (u : Ledger) (tx : Tx) (height : Nat) : Ledger :=
  addCoinsFrom (BitcoinSer.txid tx) height (isCoinBase tx)
    (if isCoinBase tx then u else spendInputs u tx.vin) 0 tx.vout

/-- The `CTxUndo` of a transaction: the coins its inputs spend. -/
def txUndo (u : Ledger) (tx : Tx) : List Coin := tx.vin.map fun i => accessCoin u i.prevout

/-- `CBlockUndo`: one `CTxUndo` per non-coinbase transaction, in block order. -/
abbrev BlockUndo := List (List Coin)

/-- Two ledgers with the same coins. -/
def Equiv (u v : Ledger) : Prop := ∀ op, getCoin u op = getCoin v op

/-- The pairwise-distinct-keys invariant. -/
def keysNodup (u : Ledger) : Prop := (u.map Prod.fst).Nodup

/-! ### `CheckTxInputs` and the per-transaction checks of `ConnectBlock` -/

def inputsLoop (u : Ledger) (spendHeight : Nat) : List TxIn → Int → Option Int
  | [], acc => some acc
  | i :: rest, acc =>
    match getCoin u i.prevout with
    | none => none
    | some coin =>
      if coin.isCoinbase && decide (spendHeight - coin.height < COINBASE_MATURITY) then none
      else
        let acc' := acc + coin.out.nValue
        if !moneyRange coin.out.nValue || !moneyRange acc' then none
        else inputsLoop u spendHeight rest acc'

/-- `Consensus::CheckTxInputs`: the fee on success. -/
def checkTxInputs (u : Ledger) (tx : Tx) (spendHeight : Nat) : Option Int :=
  if !(tx.vin.all fun i => haveCoin u i.prevout) then none
  else match inputsLoop u spendHeight tx.vin 0 with
    | none => none
    | some valueIn =>
      if valueIn < valueOut tx then none
      else if !moneyRange (valueIn - valueOut tx) then none
      else some (valueIn - valueOut tx)

/-- `GetTransactionSigOpCost(tx, view, flags)`. -/
def txSigOpCost (f : BitcoinActivation.ScriptFlags) (u : Ledger) (tx : Tx) : Nat :=
  legacySigOpCount tx * WITNESS_SCALE_FACTOR +
  (if isCoinBase tx then 0
   else
     (if f.p2sh then
        (tx.vin.map fun i => p2shSigOpCount (accessCoin u i.prevout).out.scriptPubKey i.scriptSig).sum *
          WITNESS_SCALE_FACTOR
      else 0) +
     (tx.vin.map fun i => countWitnessSigOps f i.scriptSig (accessCoin u i.prevout).out.scriptPubKey i.witness).sum)

/-- `SequenceLocks(tx, nLockTimeFlags, prevheights, *pindex)` through the BIP68 mission's
transcription; `mtp h` is the median time past of the chain at height `h`. -/
def sequenceLocksOk (u : Ledger) (height : Nat) (mtp : Nat → Nat) (lockTimeFlags : Nat) (tx : Tx) : Bool :=
  BitcoinBIP68.sequenceLocks (BitVec.ofNat 32 tx.version) (BitVec.ofNat 32 lockTimeFlags) ⟨height, mtp⟩
    (tx.vin.map fun i => ⟨BitVec.ofNat 32 i.nSequence, (accessCoin u i.prevout).height⟩)

/-- `CheckInputScripts`: every input's script verifies under the block's flags, with the complete
`VerifyScript` (Taproot branch included) and the spent outputs for the BIP341 hash. -/
def inputScriptsOk (f : BitcoinActivation.ScriptFlags) (u : Ledger) (tx : Tx) : Bool :=
  let spent := tx.vin.map fun i => (accessCoin u i.prevout).out
  (List.range tx.vin.length).all fun n =>
    let i := tx.vin.getD n ⟨⟨[], 0⟩, [], 0, []⟩
    let coin := accessCoin u i.prevout
    BitcoinTaproot.verifyScriptFull spent ⟨f, tx, n, coin.out.nValue⟩ i.scriptSig coin.out.scriptPubKey i.witness

/-- The accumulator of the `ConnectBlock` loop. -/
structure LoopState where
  utxo : Ledger
  fees : Int
  sigOps : Nat
  undo : BlockUndo

/-- The transaction loop of `ConnectBlock`, in source order: `CheckTxInputs`, the fee range,
`SequenceLocks`, the sigop budget, `CheckInputScripts`, `UpdateCoins`. -/
def connectLoop (f : BitcoinActivation.ScriptFlags) (height : Nat) (mtp : Nat → Nat) (lockTimeFlags : Nat) :
    LoopState → List Tx → Option LoopState
  | st, [] => some st
  | st, tx :: rest =>
    let step : Option (Int × BlockUndo) :=
      if isCoinBase tx then some (st.fees, st.undo)
      else match checkTxInputs st.utxo tx height with
        | none => none
        | some fee =>
          if !moneyRange (st.fees + fee) then none
          else if !sequenceLocksOk st.utxo height mtp lockTimeFlags tx then none
          else some (st.fees + fee, st.undo ++ [txUndo st.utxo tx])
    match step with
    | none => none
    | some (fees, undo) =>
      let sigOps := st.sigOps + txSigOpCost f st.utxo tx
      if MAX_BLOCK_SIGOPS_COST < sigOps then none
      else if !isCoinBase tx && !inputScriptsOk f st.utxo tx then none
      else connectLoop f height mtp lockTimeFlags ⟨updateCoins st.utxo tx height, fees, sigOps, undo⟩ rest

/-! ### Chain state -/

/-- A validated chain: its headers from the genesis to the tip, and the UTXO set. -/
structure ChainState where
  headers : List Header
  utxo : Ledger

/-- Genesis initialization: the genesis header, and an empty UTXO set (the genesis coinbase is not
spendable). -/
def initialState : ChainState := ⟨[BitcoinSer.genesisHeader], []⟩

def ChainState.tipHeight (S : ChainState) : Nat := S.headers.length - 1
def ChainState.tip (S : ChainState) : Header := S.headers.getLastD BitcoinSer.genesisHeader
def ChainState.tipHash (S : ChainState) : Bytes := BitcoinSer.headerHash S.tip
/-- The height of the next block. -/
def ChainState.nextHeight (S : ChainState) : Nat := S.headers.length
/-- The times of the blocks at heights `0..h`, most recent first. -/
def ChainState.timesTo (S : ChainState) (h : Nat) : List Int :=
  ((S.headers.take (h + 1)).map fun hd => (hd.time : Int)).reverse
/-- `GetMedianTimePast` of the block at height `h`. -/
def ChainState.mtpAt (S : ChainState) (h : Nat) : Int := BitcoinHeader.medianTimePast (S.timesTo h)
/-- The median time past of the tip. -/
def ChainState.mtp (S : ChainState) : Int := S.mtpAt S.tipHeight
/-- The `Context.mtp` function of the BIP68 mission (times are non-negative on any real chain). -/
def ChainState.mtpNat (S : ChainState) (h : Nat) : Nat := (S.mtpAt h).toNat
/-- `GetNextWorkRequired(pindexLast, …)`: the first block of the period is the ancestor at
`nHeight - 2015`. -/
def ChainState.requiredBits (S : ChainState) : BitVec 32 :=
  let first := (S.headers.getD (S.tipHeight - (BitcoinPow.difficultyAdjustmentInterval - 1)) BitcoinSer.genesisHeader)
  BitcoinPow.nextWorkRequired S.tipHeight (BitVec.ofNat 32 S.tip.bits) S.tip.time first.time
/-- `GetBlockProof`: `(~target / (target + 1)) + 1` on 256-bit words, zero for an invalid target. -/
def blockProof (bits : Nat) : Nat :=
  match BitcoinPow.deriveTarget (BitVec.ofNat 32 bits) with
  | none => 0
  | some t => (BitcoinPow.width - 1 - t) / (t + 1) + 1
/-- `nChainWork`. -/
def ChainState.chainWork (S : ChainState) : Nat := (S.headers.map fun h => blockProof h.bits).sum

/-- The hash of a block as a 256-bit number (`uint256` is little-endian). -/
def hashValue (h : Header) : Nat := BitcoinSer.leVal (BitcoinSer.headerHash h)

/-! ### `CheckBlock` -/

def merkleCombine (a b : Bytes) : Bytes := BitcoinSer.hash256 (a ++ b)
def zeroHash : Bytes := List.replicate 32 0

/-- `BlockMerkleRoot(block, &mutated)`. -/
def blockMerkleRoot (b : Block) : Bytes × Bool :=
  BitcoinMerkle.computeMerkleRoot merkleCombine zeroHash (b.vtx.map BitcoinSer.txid)
/-- `BlockWitnessMerkleRoot`: the coinbase's witness hash is zero. -/
def blockWitnessMerkleRoot (b : Block) : Bytes :=
  (BitcoinMerkle.computeMerkleRoot merkleCombine zeroHash (zeroHash :: (b.vtx.drop 1).map BitcoinSer.wtxid)).1

/-- `CheckProofOfWork(block.GetHash(), block.nBits)`. -/
def checkHeaderPow (h : Header) : Bool := BitcoinPow.checkProofOfWork (hashValue h) (BitVec.ofNat 32 h.bits)

/-- `CheckBlock` with `fCheckPOW` and `fCheckMerkleRoot`, in source order. -/
def checkBlock (b : Block) : Bool :=
  checkHeaderPow b.header &&
  decide ((blockMerkleRoot b).1 = b.header.merkleRoot) && !(blockMerkleRoot b).2 &&
  !b.vtx.isEmpty && decide (b.vtx.length * WITNESS_SCALE_FACTOR ≤ MAX_BLOCK_WEIGHT) &&
  decide ((BitcoinSer.serBlock false b).length * WITNESS_SCALE_FACTOR ≤ MAX_BLOCK_WEIGHT) &&
  isCoinBase (b.vtx.headD BitcoinSer.genesisCoinbase) &&
  (b.vtx.drop 1).all (fun tx => !isCoinBase tx) &&
  b.vtx.all checkTransaction &&
  decide ((b.vtx.map legacySigOpCount).sum * WITNESS_SCALE_FACTOR ≤ MAX_BLOCK_SIGOPS_COST)

/-! ### `ContextualCheckBlock` -/

/-- `CScript() << nHeight` for a non-negative height. -/
def heightScript (n : Nat) : Bytes :=
  if n = 0 then [0] else if n ≤ 16 then [BitVec.ofNat 8 (0x50 + n)]
  else BitcoinSig.pushBytes (BitcoinScript.serialize n)

/-- `GetWitnessCommitmentIndex`: the last coinbase output of at least 38 bytes starting with
`6a 24 aa 21 a9 ed`. -/
def isCommitmentOutput (o : TxOut) : Bool :=
  decide (MINIMUM_WITNESS_COMMITMENT ≤ o.scriptPubKey.length) &&
  decide (o.scriptPubKey.take 6 = [0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed])

def witnessCommitmentIndex (b : Block) : Option Nat :=
  match b.vtx with
  | [] => none
  | cb :: _ => ((List.range cb.vout.length).filter fun i => isCommitmentOutput (cb.vout.getD i ⟨0, []⟩)).getLast?

/-- `CheckWitnessMalleation(block, expect_witness_commitment)`. -/
def checkWitnessMalleation (b : Block) (expect : Bool) : Bool :=
  let noWitness := b.vtx.all fun tx => !tx.hasWitness
  if expect then
    match witnessCommitmentIndex b with
    | none => noWitness
    | some pos =>
      let cb := b.vtx.headD BitcoinSer.genesisCoinbase
      let stack := (cb.vin.headD ⟨⟨[], 0⟩, [], 0, []⟩).witness
      match stack with
      | [nonce] =>
        decide (nonce.length = 32) &&
        decide (BitcoinSer.hash256 (blockWitnessMerkleRoot b ++ nonce) =
                ((cb.vout.getD pos ⟨0, []⟩).scriptPubKey.drop 6).take 32)
      | _ => false
  else noWitness

/-- `ContextualCheckBlock(block, pindexPrev)`: finality against the lock-time cutoff, the BIP34
coinbase height, the witness commitment, and the weight limit. -/
def contextualCheckBlock (S : ChainState) (b : Block) : Bool :=
  let height := S.nextHeight
  let cutoff : Int := if BitcoinActivation.activeAfter S.tipHeight .csv then S.mtp else (b.header.time : Int)
  b.vtx.all (fun tx => isFinalTx tx height cutoff) &&
  (!BitcoinActivation.activeAfter S.tipHeight .heightInCB ||
    (heightScript height).isPrefixOf ((b.vtx.headD BitcoinSer.genesisCoinbase).vin.headD ⟨⟨[], 0⟩, [], 0, []⟩).scriptSig) &&
  checkWitnessMalleation b (BitcoinActivation.activeAfter S.tipHeight .segwit) &&
  decide (BitcoinSer.blockWeight b ≤ MAX_BLOCK_WEIGHT)

/-! ### `ConnectBlock` -/

/-- `fEnforceBIP30 || nHeight >= BIP34_IMPLIES_BIP30_LIMIT`: the BIP30 scan is performed unless the
block is one of the two repeats or the BIP34 activation block is an ancestor with the expected hash,
and always from height 1983702 on. -/
def bip30Checked (S : ChainState) (height : Nat) (hash : Bytes) : Bool :=
  let bip34Ancestor := match S.headers[BitcoinHeader.BIP34Height]? with
    | some h => decide (BitcoinSer.headerHash h = bip34Hash)
    | none => false
  (!isBIP30Repeat height hash && !bip34Ancestor) || decide (BIP34_IMPLIES_BIP30_LIMIT ≤ height)

/-- The BIP30 scan: no output of the block already exists as an unspent coin. -/
def bip30Ok (u : Ledger) (b : Block) : Bool :=
  b.vtx.all fun tx => (List.range tx.vout.length).all fun o => !haveCoin u ⟨BitcoinSer.txid tx, o⟩

/-- `ConnectBlock` after `CheckBlock`: the genesis shortcut, BIP30, the flags, the loop, the coinbase
bound. Returns the new ledger and the undo data. -/
def connectBlock (S : ChainState) (b : Block) : Option (Ledger × BlockUndo) :=
  let hash := BitcoinSer.headerHash b.header
  let height := S.nextHeight
  if hash = BitcoinSer.genesisHash then some (S.utxo, [])
  else if bip30Checked S height hash && !bip30Ok S.utxo b then none
  else
    let flags := BitcoinActivation.blockScriptFlags height (scriptException hash)
    match connectLoop flags height S.mtpNat (BitcoinActivation.lockTimeFlags height) ⟨S.utxo, 0, 0, []⟩ b.vtx with
    | none => none
    | some st =>
      if valueOut (b.vtx.headD BitcoinSer.genesisCoinbase) >
           st.fees + (BitcoinSubsidy.coreSubsidy height : Int) then none
      else some (st.utxo, st.undo)

/-! ### The complete validation path -/

/-- The outcome of offering a block to a chain state: accepted with the new state and undo data;
rejected as invalid; rejected only because its time is too far in the future (`BLOCK_TIME_FUTURE`);
or not building on the tip (`BLOCK_MISSING_PREV`). -/
inductive Outcome where
  | accept (S' : ChainState) (undo : BlockUndo)
  | invalid
  | futureTime
  | missingPrev


/-- `AcceptBlockHeader` for a header on top of the tip: `CheckBlockHeader` (proof of work), the
previous-block lookup, then `ContextualCheckBlockHeader` in source order (`nBits`, `time-too-old`,
`time-too-new`, the version floors). `now` is the local clock. -/
def acceptHeader (S : ChainState) (h : Header) (now : Int) : Outcome :=
  if !checkHeaderPow h then .invalid
  else if h.prevBlock ≠ S.tipHash then .missingPrev
  else if BitVec.ofNat 32 h.bits ≠ S.requiredBits then .invalid
  else if (h.time : Int) ≤ S.mtp then .invalid
  else if now + MAX_FUTURE_BLOCK_TIME < (h.time : Int) then .futureTime
  else if BitcoinHeader.versionOutdated h.version S.tipHeight then .invalid
  else .accept S []

/-- The source-linked validation outcome `C(S, B, t)`: the header path, `CheckBlock`,
`ContextualCheckBlock`, `ConnectBlock`. -/
def validate (S : ChainState) (b : Block) (now : Int) : Outcome :=
  match acceptHeader S b.header now with
  | .accept _ _ =>
    if !checkBlock b then .invalid
    else if !contextualCheckBlock S b then .invalid
    else match connectBlock S b with
      | none => .invalid
      | some (u, undo) => .accept ⟨S.headers ++ [b.header], u⟩ undo
  | o => o

def accepts (S : ChainState) (b : Block) (now : Int) : Prop := ∃ S' undo, validate S b now = .accept S' undo

/-- Reachability from the genesis state through accepted blocks. -/
inductive Reachable : ChainState → Prop
  | genesis : Reachable initialState
  | step {S : ChainState} {b : Block} {now : Int} {S' : ChainState} {undo : BlockUndo} :
      Reachable S → validate S b now = .accept S' undo → Reachable S'

/-! ### `DisconnectBlock` -/

/-- `ApplyTxInUndo`: restore a spent coin; `none` is `DISCONNECT_FAILED`, the flag is `fClean`. -/
def applyTxInUndo (u : Ledger) (undo : Coin) (out : OutPoint) : Option (Ledger × Bool) :=
  let clean := !haveCoin u out
  let undo? : Option Coin :=
    if undo.height = 0 then
      match u.find? (fun e => e.1.hash = out.hash) with
      | some (_, alt) => some { undo with height := alt.height, isCoinbase := alt.isCoinbase }
      | none => none
    else some undo
  match undo? with
  | none => none
  | some c => some (addCoin u out c, clean)

/-- Restore the inputs of a transaction in reverse order. -/
def restoreInputs (u : Ledger) : List (TxIn × Coin) → Option (Ledger × Bool)
  | [] => some (u, true)
  | (i, c) :: rest =>
    match restoreInputs u rest with
    | none => none
    | some (u', clean) =>
      match applyTxInUndo u' c i.prevout with
      | none => none
      | some (u'', clean') => some (u'', clean && clean')

/-- Spend the (spendable) outputs of a transaction, checking each against the block. -/
def spendOutputs (u : Ledger) (txid : Bytes) (height : Nat) (cb : Bool) (exception : Bool) :
    List TxOut → Nat → Ledger × Bool
  | [], _ => (u, true)
  | o :: rest, i =>
    let (u', clean) :=
      if isUnspendable o.scriptPubKey then (u, true)
      else
        let op : OutPoint := ⟨txid, i⟩
        let ok := match getCoin u op with
          | none => false
          | some coin => decide (coin.out = o) && decide (coin.height = height) && decide (coin.isCoinbase = cb)
        (spendCoin u op, ok || exception)
    let (u'', clean') := spendOutputs u' txid height cb exception rest (i + 1)
    (u'', clean && clean')

/-- Undo one transaction: its outputs, then (for a non-coinbase) its inputs. -/
def disconnectTx (u : Ledger) (height : Nat) (exception : Bool) (tx : Tx) (undo : Option (List Coin)) :
    Option (Ledger × Bool) :=
  let cb := isCoinBase tx
  let (u', clean) := spendOutputs u (BitcoinSer.txid tx) height cb (cb && exception) tx.vout 0
  match undo with
  | none => some (u', clean)
  | some coins =>
    if coins.length ≠ tx.vin.length then none
    else match restoreInputs u' (tx.vin.zip coins) with
      | none => none
      | some (u'', clean') => some (u'', clean && clean')

def disconnectTxs (height : Nat) (exception : Bool) : Ledger → List (Tx × Option (List Coin)) → Option (Ledger × Bool)
  | u, [] => some (u, true)
  | u, (tx, undo) :: rest =>
    match disconnectTx u height exception tx undo with
    | none => none
    | some (u', clean) =>
      match disconnectTxs height exception u' rest with
      | none => none
      | some (u'', clean') => some (u'', clean && clean')

/-- `DisconnectBlock(block, pindex, view)`: the undo-count test, the two unspendable-coinbase
exceptions, and the transactions in reverse order. -/
def disconnectBlock (u : Ledger) (height : Nat) (hash : Bytes) (b : Block) (undo : BlockUndo) :
    Option (Ledger × Bool) :=
  if undo.length + 1 ≠ b.vtx.length then none
  else disconnectTxs height (isBIP30Unspendable height hash) u
    ((b.vtx.zip (none :: undo.map some)).reverse)

/-! ### The declarative specification `V(S, B, t)` and `ApplySpec` -/

/-- Transaction well-formedness, as a predicate. -/
def TxSpec (tx : Tx) : Prop :=
  tx.vin ≠ [] ∧ tx.vout ≠ [] ∧
  (BitcoinSer.serTx false tx).length * WITNESS_SCALE_FACTOR ≤ MAX_BLOCK_WEIGHT ∧
  (∀ o ∈ tx.vout, 0 ≤ o.nValue ∧ o.nValue ≤ MAX_MONEY) ∧ valueOut tx ≤ MAX_MONEY ∧
  (tx.vin.map TxIn.prevout).Nodup ∧
  (isCoinBase tx = true → ∀ i ∈ tx.vin, 2 ≤ i.scriptSig.length ∧ i.scriptSig.length ≤ 100) ∧
  (isCoinBase tx = false → ∀ i ∈ tx.vin, outPointNull i.prevout = false)

/-- The sum of the values of the coins spent by the inputs. -/
def valueIn (u : Ledger) : List TxIn → Int
  | [] => 0
  | i :: rest => (accessCoin u i.prevout).out.nValue + valueIn u rest

/-- The fee of a transaction against a ledger. -/
def feeOf (u : Ledger) (tx : Tx) : Int := valueIn u tx.vin - valueOut tx

/-- Admissibility of one non-coinbase transaction against the ledger `u` at `height`: every input
spends an existing, mature coin of valid value; the total input value is in range and covers the
outputs; the fee is in range; BIP68 holds (the specification form of the BIP68 mission); every
input script verifies. -/
def TxInputsSpec (f : BitcoinActivation.ScriptFlags) (u : Ledger) (height : Nat) (mtp : Nat → Nat)
    (lockTimeFlags : Nat) (tx : Tx) : Prop :=
  (∀ i ∈ tx.vin, ∃ c, getCoin u i.prevout = some c ∧
      (c.isCoinbase = true → c.height + COINBASE_MATURITY ≤ height) ∧ 0 ≤ c.out.nValue ∧ c.out.nValue ≤ MAX_MONEY) ∧
  valueIn u tx.vin ≤ MAX_MONEY ∧ valueOut tx ≤ valueIn u tx.vin ∧
  BitcoinBIP68.satisfiesBIP68 (BitVec.ofNat 32 tx.version) (BitVec.ofNat 32 lockTimeFlags) ⟨height, mtp⟩
    (tx.vin.map fun i => ⟨BitVec.ofNat 32 i.nSequence, (accessCoin u i.prevout).height⟩) ∧
  ∀ n, n < tx.vin.length →
    let i := tx.vin.getD n ⟨⟨[], 0⟩, [], 0, []⟩
    let coin := accessCoin u i.prevout
    BitcoinTaproot.verifyScriptFull (tx.vin.map fun j => (accessCoin u j.prevout).out)
      ⟨f, tx, n, coin.out.nValue⟩ i.scriptSig coin.out.scriptPubKey i.witness = true

/-- The transactions of a block, applied in order: each is admissible against the ledger produced
by its predecessors, the accumulated fees and sigop cost stay within their limits. -/
def TxsSpec (f : BitcoinActivation.ScriptFlags) (height : Nat) (mtp : Nat → Nat) (lockTimeFlags : Nat) :
    Ledger → Int → Nat → List Tx → Prop
  | _, _, _, [] => True
  | u, fees, sigOps, tx :: rest =>
    (isCoinBase tx = false → TxInputsSpec f u height mtp lockTimeFlags tx ∧ fees + feeOf u tx ≤ MAX_MONEY) ∧
    sigOps + txSigOpCost f u tx ≤ MAX_BLOCK_SIGOPS_COST ∧
    TxsSpec f height mtp lockTimeFlags (updateCoins u tx height)
      (if isCoinBase tx then fees else fees + feeOf u tx) (sigOps + txSigOpCost f u tx) rest

/-- The ledger after applying the transactions in order. -/
def applyTxs (height : Nat) : Ledger → List Tx → Ledger
  | u, [] => u
  | u, tx :: rest => applyTxs height (updateCoins u tx height) rest

/-- The total fees of a block's non-coinbase transactions, against the running ledger. -/
def totalFees (height : Nat) : Ledger → List Tx → Int
  | _, [] => 0
  | u, tx :: rest => (if isCoinBase tx then 0 else feeOf u tx) + totalFees height (updateCoins u tx height) rest

/-- The declarative state transition `ApplySpec(S, B)`. -/
def applySpec (S : ChainState) (b : Block) : ChainState :=
  if BitcoinSer.headerHash b.header = BitcoinSer.genesisHash then ⟨S.headers ++ [b.header], S.utxo⟩
  else ⟨S.headers ++ [b.header], applyTxs S.nextHeight S.utxo b.vtx⟩

/-- The header rules as a predicate: a valid compact target met by the hash (the PoW mission's
specification form), the tip as parent, the required difficulty, the median-time-past floor, the
clock ceiling, and the version floors. -/
def HeaderSpec (S : ChainState) (h : Header) (now : Int) : Prop :=
  (BitcoinPow.compactNegative (BitVec.ofNat 32 h.bits) = false ∧
   BitcoinPow.compactOverflow (BitVec.ofNat 32 h.bits) = false ∧
   0 < BitcoinPow.specTarget (BitVec.ofNat 32 h.bits) ∧
   BitcoinPow.specTarget (BitVec.ofNat 32 h.bits) ≤ BitcoinPow.powLimit ∧
   hashValue h ≤ BitcoinPow.specTarget (BitVec.ofNat 32 h.bits)) ∧
  h.prevBlock = S.tipHash ∧
  BitVec.ofNat 32 h.bits = S.requiredBits ∧
  S.mtp < (h.time : Int) ∧ (h.time : Int) ≤ now + MAX_FUTURE_BLOCK_TIME ∧
  ¬ ((h.version < 2 ∧ BitcoinHeader.BIP34Height ≤ S.tipHeight + 1) ∨
     (h.version < 3 ∧ BitcoinHeader.BIP66Height ≤ S.tipHeight + 1) ∨
     (h.version < 4 ∧ BitcoinHeader.BIP65Height ≤ S.tipHeight + 1))

/-- The context-free block rules as a predicate. -/
def BlockSpec (b : Block) : Prop :=
  b.vtx ≠ [] ∧
  (blockMerkleRoot b).1 = b.header.merkleRoot ∧ (blockMerkleRoot b).2 = false ∧
  b.vtx.length * WITNESS_SCALE_FACTOR ≤ MAX_BLOCK_WEIGHT ∧
  (BitcoinSer.serBlock false b).length * WITNESS_SCALE_FACTOR ≤ MAX_BLOCK_WEIGHT ∧
  (∀ tx ∈ b.vtx.take 1, isCoinBase tx = true) ∧ (∀ tx ∈ b.vtx.drop 1, isCoinBase tx = false) ∧
  (∀ tx ∈ b.vtx, TxSpec tx) ∧
  (b.vtx.map legacySigOpCount).sum * WITNESS_SCALE_FACTOR ≤ MAX_BLOCK_SIGOPS_COST

/-- The contextual block rules as a predicate. -/
def ContextSpec (S : ChainState) (b : Block) : Prop :=
  let height := S.nextHeight
  let cutoff : Int := if BitcoinActivation.activeAfter S.tipHeight .csv then S.mtp else (b.header.time : Int)
  (∀ tx ∈ b.vtx, isFinalTx tx height cutoff = true) ∧
  (BitcoinActivation.activeAfter S.tipHeight .heightInCB = true →
    ∀ cb ∈ b.vtx.take 1, ∀ i ∈ cb.vin.take 1, (heightScript height).isPrefixOf i.scriptSig = true) ∧
  checkWitnessMalleation b (BitcoinActivation.activeAfter S.tipHeight .segwit) = true ∧
  BitcoinSer.blockWeight b ≤ MAX_BLOCK_WEIGHT

/-- The ledger rules as a predicate: BIP30 where it applies, the transaction sequence, and the
coinbase bound against the specification subsidy. -/
def LedgerSpec (S : ChainState) (b : Block) : Prop :=
  let hash := BitcoinSer.headerHash b.header
  let height := S.nextHeight
  let flags := BitcoinActivation.blockScriptFlags height (scriptException hash)
  hash = BitcoinSer.genesisHash ∨
  ((bip30Checked S height hash = true →
      ∀ tx ∈ b.vtx, ∀ o, o < tx.vout.length → getCoin S.utxo ⟨BitcoinSer.txid tx, o⟩ = none) ∧
   TxsSpec flags height S.mtpNat (BitcoinActivation.lockTimeFlags height) S.utxo 0 0 b.vtx ∧
   ∀ cb ∈ b.vtx.take 1,
     valueOut cb ≤ totalFees height S.utxo b.vtx + (BitcoinSubsidy.specSubsidy height : Int))

/-- Declarative admissibility `V(S, B, t)`. -/
def Valid (S : ChainState) (b : Block) (now : Int) : Prop :=
  HeaderSpec S b.header now ∧ BlockSpec b ∧ ContextSpec S b ∧ LedgerSpec S b

/-- A ledger with distinct keys whose coins are spendable and were created above the genesis. -/
def LedgerOk (u : Ledger) : Prop :=
  keysNodup u ∧ ∀ e ∈ u, e.2.height ≠ 0 ∧ isUnspendable e.2.out.scriptPubKey = false

/-- The well-formedness every reachable state enjoys: a non-empty header list starting at the
genesis, distinct ledger keys, and spendable coins created at heights `1..tip`. -/
def WellFormed (S : ChainState) : Prop :=
  S.headers.head? = some BitcoinSer.genesisHeader ∧ keysNodup S.utxo ∧
  ∀ e ∈ S.utxo, 1 ≤ e.2.height ∧ e.2.height ≤ S.tipHeight ∧ isUnspendable e.2.out.scriptPubKey = false

end BitcoinBlockV2


