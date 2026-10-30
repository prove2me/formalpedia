-- Prove2me | Definitions.Def_BitcoinFunding
-- name    : BitcoinFunding
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T19:38:59.066178+00:00
-- url     : https://prove2.me/theorems/a5a5e226-9d48-4bda-8cea-326625f7a630
-- title:
--   The Lightning funding output script and its spending condition
-- statement:
--   Names over the script, verification and `to_local` missions.
--
--   **`fundingScript pubkey1 pubkey2`** / **`fundingBytes`** — the BOLT #3 funding witness script `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG`, parsed and as `CScript` serializes it (`2` as `OP_2`).
--
--   **`FundingSpend f o pubkey1 pubkey2 st`** — for a witness stack `st` (top first): `st = [sig2, sig1, dummy]` with `sig1` valid for `pubkey1`, `sig2` valid for `pubkey2` (the oracle's `checkSig`), and an empty dummy when `NULLDUMMY` is enforced. In `CScriptWitness` order this is BOLT #3's `0 <signature_for_pubkey1> <signature_for_pubkey2>`.
--
--   **Formalization Note.** `numInstr`, `numBytes` are the `to_local` mission's; `multisigLoop`, `Flags`, `Oracle`, `evalScript` the script mission's; `verifyScript`, `topTrue` the verification mission's. Only `Std` is imported.
-- source:
--   BOLT #3, Funding Transaction Output: https://github.com/lightning/bolts/blob/master/03-transactions.md#funding-transaction-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKMULTISIG), ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP141, BIP147

import Definitions.Def_BitcoinHtlc

/-!
# The Lightning funding output

A channel's funds sit in the funding transaction's output, a pay-to-witness-script-hash of the
2-of-2 script `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG` (BOLT #3, with the keys in lexicographic
order). Every commitment transaction spends it with the witness `0 <sig1> <sig2>`. This file states
the script and its single spending condition as the script and verification missions model them.
-/

namespace BitcoinFunding

open BitcoinScript BitcoinSig BitcoinVerify BitcoinToLocal

/-- The BOLT #3 funding witness script, parsed: `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG`. -/
def fundingScript (pubkey1 pubkey2 : Bytes) : Script :=
  [numInstr 2, .push pubkey1, .push pubkey2, numInstr 2, .op OP_CHECKMULTISIG]

/-- The funding witness script as `CScript` serializes it. -/
def fundingBytes (pubkey1 pubkey2 : Bytes) : Bytes :=
  numBytes 2 ++ pushBytes pubkey1 ++ pushBytes pubkey2 ++ numBytes 2 ++ [OP_CHECKMULTISIG]

/-- The only way to satisfy the funding script with a witness stack `st` (top first): three
elements `[sig2, sig1, dummy]`, `sig1` valid for `pubkey1`, `sig2` valid for `pubkey2`, and an empty
dummy when `NULLDUMMY` is enforced. (In `CScriptWitness` order the witness is `dummy sig1 sig2`.) -/
def FundingSpend (f : Flags) (o : Oracle) (pubkey1 pubkey2 : Bytes) (st : List Bytes) : Prop :=
  ∃ sig1 sig2 dummy, st = [sig2, sig1, dummy] ∧
    o.checkSig sig1 pubkey1 = some true ∧ o.checkSig sig2 pubkey2 = some true ∧
    (f.nulldummy = true → dummy = [])

end BitcoinFunding


