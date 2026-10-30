-- Prove2me | Definitions.Def_BitcoinToLocal
-- name    : BitcoinToLocal
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T15:09:14.583039+00:00
-- url     : https://prove2.me/theorems/c1d7f288-3837-4d38-9fc8-9ef65c05f5ec
-- title:
--   The Lightning to_local witness script and its two spending conditions
-- statement:
--   Names over the script, signature and verification missions; nothing of Core is re-transcribed.
--
--   **`numInstr n`** / **`numBytes n`** — what `CScript::operator<<(int64_t)` emits for a small integer: `OP_1NEGATE` for $-1$, `OP_1` … `OP_16` for $1$ … $16$, and the `CScriptNum` push otherwise (the empty push for $0$), as an instruction and as bytes.
--
--   **`toLocalScript rev delay dpk`** — the BOLT #3 `to_local` witness script `OP_IF <rev> OP_ELSE <delay> OP_CHECKSEQUENCEVERIFY OP_DROP <dpk> OP_ENDIF OP_CHECKSIG`, parsed; **`toLocalBytes rev delay dpk`** — the same as `CScript` serializes it.
--
--   **`CsvPasses f o delay`** — what `OP_CHECKSEQUENCEVERIFY` lets through for the operand `delay` under flags $f$ and oracle $o$: the `CHECKSEQUENCEVERIFY` flag is off, or `delay` is non-negative and either carries the disable bit (bit 31) or satisfies the oracle's `checkSequence`.
--
--   **`SpendCondition f o rev delay dpk b sig`** — the revocation path ($b$ true and `o.checkSig sig rev = some true`) or the delayed path ($b$ false, `CsvPasses f o delay`, and `o.checkSig sig dpk = some true`), for the witness stack `[b, sig]` (top first).
--
--   **`inputSequence tx nIn`** — the `nSequence` of input `nIn` of a transaction (an empty input when out of range).
--
--   **Formalization Note.** `Flags`, `Oracle`, `evalScript`, `serialize`, `castToBool` are the script mission's; `legacyOracle`, `checkSequence`, `parseScript`, `pushBytes` the signature mission's; `verifyScript`, `executeWitnessScriptV0`, `topTrue`, `witnessBytes` the verification mission's. Only `Std` is imported. `MINIMALIF` is a policy flag and is off, so any true value selects the revocation branch under consensus.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'to_local Output': https://github.com/lightning/bolts/blob/master/03-transactions.md#to_local-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_IF/OP_ELSE/OP_ENDIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckSequence, ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); CScript::operator<<(int64_t) (script/script.h); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinVerify

/-!
# The Lightning `to_local` output under Bitcoin's script interpreter

BOLT #3 (Lightning Network specification, *Bitcoin Transaction and Script Formats*) gives the
`to_local` output of a commitment transaction the witness script

```
OP_IF
    <revocationpubkey>
OP_ELSE
    `to_self_delay`
    OP_CHECKSEQUENCEVERIFY
    OP_DROP
    <local_delayedpubkey>
OP_ENDIF
OP_CHECKSIG
```

paid to as pay-to-witness-script-hash. The intent is that the output can be spent either by the
counterparty with the revocation key at any time, or by the local node with its delayed key once
`to_self_delay` blocks have passed. This file states that script as the script and verification
missions model it, so that the two spending conditions can be proved to be exactly what the
interpreter enforces.
-/

namespace BitcoinToLocal

open BitcoinScript BitcoinSig BitcoinVerify

/-- `CScript::operator<<(int64_t n)`: `OP_1NEGATE` for `-1`, `OP_1` … `OP_16` for `1` … `16`, and the
`CScriptNum` push otherwise (`OP_0`, the empty push, for `0`). -/
def numInstr (n : Int) : Instr :=
  if n = -1 ∨ (1 ≤ n ∧ n ≤ 16) then .op (BitVec.ofNat 8 (n + (OP_1.toNat - 1)).toNat)
  else .push (serialize n)

/-- The bytes `CScript::operator<<(int64_t n)` appends. -/
def numBytes (n : Int) : Bytes :=
  if n = -1 ∨ (1 ≤ n ∧ n ≤ 16) then [BitVec.ofNat 8 (n + (OP_1.toNat - 1)).toNat]
  else pushBytes (serialize n)

/-- The BOLT #3 `to_local` witness script, parsed. -/
def toLocalScript (revocationPubkey : Bytes) (toSelfDelay : Int) (localDelayedPubkey : Bytes) : Script :=
  [.op OP_IF, .push revocationPubkey, .op OP_ELSE, numInstr toSelfDelay, .op OP_CHECKSEQUENCEVERIFY,
   .op OP_DROP, .push localDelayedPubkey, .op OP_ENDIF, .op OP_CHECKSIG]

/-- The BOLT #3 `to_local` witness script, as `CScript` serializes it. -/
def toLocalBytes (revocationPubkey : Bytes) (toSelfDelay : Int) (localDelayedPubkey : Bytes) : Bytes :=
  [OP_IF] ++ pushBytes revocationPubkey ++ [OP_ELSE] ++ numBytes toSelfDelay ++
    [OP_CHECKSEQUENCEVERIFY, OP_DROP] ++ pushBytes localDelayedPubkey ++ [OP_ENDIF, OP_CHECKSIG]

/-- What `OP_CHECKSEQUENCEVERIFY` lets through for the operand `delay`: nothing is checked when the
`CHECKSEQUENCEVERIFY` flag is off; otherwise the operand must be non-negative and either carry the
disable flag (bit 31) or satisfy the checker's `CheckSequence`. -/
def CsvPasses (f : Flags) (o : Oracle) (delay : Int) : Prop :=
  f.csv = false ∨ (0 ≤ delay ∧ ((delay.toNat &&& BitcoinScript.SEQUENCE_LOCKTIME_DISABLE_FLAG) ≠ 0 ∨ o.checkSequence delay = true))

instance (f : Flags) (o : Oracle) (delay : Int) : Decidable (CsvPasses f o delay) := by
  unfold CsvPasses; infer_instance

/-- The two ways of satisfying the `to_local` script with the witness stack `[b, sig]` (top first):
the revocation path, `b` true and `sig` valid for the revocation key; or the delayed path, `b` false,
the delay check passing, and `sig` valid for the delayed key. -/
def SpendCondition (f : Flags) (o : Oracle) (revocationPubkey : Bytes) (toSelfDelay : Int)
    (localDelayedPubkey : Bytes) (b sig : Bytes) : Prop :=
  (castToBool b = true ∧ o.checkSig sig revocationPubkey = some true) ∨
  (castToBool b = false ∧ CsvPasses f o toSelfDelay ∧ o.checkSig sig localDelayedPubkey = some true)

/-- The `nSequence` of input `nIn` of a transaction (an empty input when out of range). -/
def inputSequence (tx : BitcoinSer.Tx) (nIn : Nat) : Nat := (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence

end BitcoinToLocal


