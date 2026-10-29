-- Prove2me | Definitions.Def_BitcoinMalleability
-- name    : BitcoinMalleability
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T00:01:11.807547+00:00
-- url     : https://prove2.me/theorems/9df80fb4-93ba-425d-a3c0-0cd5a42604d6
-- title:
--   Transaction intent: the signature-free content of a transaction, and spends of native witness programs
-- statement:
--   Three names over the serialization mission's `Tx`, the block mission's ledger, and the VerifyScript mission's `isWitnessProgram`; nothing is re-transcribed.
--
--   **`Intent`** — a record of a version, a list of (outpoint, sequence number) pairs, a list of outputs, and a lock time: what the sender decides. `scriptSig`s and witnesses are not part of it.
--
--   **`intentOf tx`** — the intent of a transaction: its version, the (prevout, `nSequence`) of each input in order, its outputs, its lock time.
--
--   **`ofIntent t`** — the canonical transaction of an intent: the same fields, every `scriptSig` empty, every witness empty.
--
--   **`SpendsWitnessPrograms u tx`** — every input of `tx` spends, in the ledger `u`, an output whose `scriptPubKey` is a native witness program (`CScript::IsWitnessProgram`: `OP_0` or `OP_1`..`OP_16` followed by a single push of 2 to 40 bytes).
--
--   **Formalization Note.** `txid` is the serialization mission's double SHA-256 of the witness-stripped serialization; `inputScriptsOk` is the block mission's `CheckInputScripts` (the complete `VerifyScript` for every input against the spent outputs); `verifyScript` is the VerifyScript mission's dispatch. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript (SCRIPT_ERR_WITNESS_MALLEATED, SCRIPT_ERR_WITNESS_MALLEATED_P2SH), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CTransaction::ComputeHash, SerializeTransaction (primitives/transaction.h, transaction.cpp); CheckInputScripts (validation.cpp); BIP141 (Transaction ID)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinVerify

/-!
# Transaction identifiers under SegWit

The txid of a transaction hashes its witness-stripped serialization, which still contains every
`scriptSig`. Before SegWit a third party could alter a signature's encoding inside a `scriptSig`
and change the txid of a valid transaction without invalidating it. For an input that spends a
native witness program, `VerifyScript` requires the `scriptSig` to be empty
(`SCRIPT_ERR_WITNESS_MALLEATED`), so nothing a signer or a third party chooses remains in the
hashed bytes. This file names the sender's intent, the part of a transaction that is not a
signature, so that the theorems can say: for such spends the txid is a function of the intent.
-/

namespace BitcoinMalleability

open BitcoinSer BitcoinBlockV2

/-- What the sender decides: the version, the outpoint and sequence number of every input, the
outputs, and the lock time. The `scriptSig`s and witnesses are not part of it. -/
structure Intent where
  version : Nat
  inputs : List (OutPoint × Nat)
  vout : List TxOut
  nLockTime : Nat
  deriving DecidableEq, Repr

/-- The intent of a transaction. -/
def intentOf (tx : Tx) : Intent :=
  ⟨tx.version, tx.vin.map fun i => (i.prevout, i.nSequence), tx.vout, tx.nLockTime⟩

/-- The canonical transaction of an intent: empty `scriptSig`s and empty witnesses. -/
def ofIntent (t : Intent) : Tx :=
  ⟨t.version, t.inputs.map fun p => ⟨p.1, [], p.2, []⟩, t.vout, t.nLockTime⟩

/-- Every input of `tx` spends, in the ledger `u`, an output whose script is a native witness
program (`CScript::IsWitnessProgram`). -/
def SpendsWitnessPrograms (u : Ledger) (tx : Tx) : Prop :=
  ∀ i ∈ tx.vin, BitcoinVerify.isWitnessProgram (accessCoin u i.prevout).out.scriptPubKey ≠ none

end BitcoinMalleability


