-- Prove2me | Definitions.Def_BitcoinScriptV2
-- name    : BitcoinScriptV2
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T23:17:56.915201+00:00
-- url     : https://prove2.me/theorems/02f764dd-50b5-4f94-8a23-8ffd4c411220
-- title:
--   The legacy script interpreter with the signature script code tracked exactly (closing limits L1 and L10)
-- statement:
--   A second interpreter over the script mission's `BitcoinScript`, whose only difference is that the signature checks see the *script code* exactly as Core computes it.
--
--   **`OracleV2`** — like the script mission's `Oracle`, but `checkSig : (scriptCode : Bytes) → (sig pk : Bytes) → Option Bool` receives the script code. **`fadSig v sc sig`** — in `SigVersion::BASE`, `FindAndDelete` of the push of `sig` from `sc`; the identity in witness v0. **`fadAll v sc sigs`** — the fold of `fadSig` over a list of signatures. **`withCode o sc`**, **`withCodeSig o v sc`** — the published `Oracle` obtained by fixing the script code (and, for `withCodeSig`, deleting the checked signature as the published model does). **`multisigSigs stack`** — the signatures an `OP_CHECKMULTISIG` will consume, read off the stack layout.
--
--   **`StateV2`** — the published `State` plus `scriptCode : Bytes`, Core's `CScript(pbegincodehash, pend)`. **`oracleAt v o s i`** — the oracle for instruction $i$: `OP_CHECKSIG(VERIFY)` see `fadSig` of the one signature, `OP_CHECKMULTISIG(VERIFY)` see `fadAll` of all their signatures (deleted before any check, as Core does), every other instruction sees the code unchanged. **`stepV2`** — the published `step` with `oracleAt`, and an executed `OP_CODESEPARATOR` resets `scriptCode` to the bytes after the opcode. **`annotate s`** — the `GetOp` parse of a byte script paired with the byte suffix after each instruction; **`runV2`**, **`evalScriptV2`**, **`legacyOracleV2`**, **`evalBytesV2`**, **`executeWitnessScriptV0V2`**, **`verifyWitnessProgramV2`**, **`verifyScriptV2`** — the verification mission's pipeline over the new evaluator (the Taproot handler unchanged).
--
--   **Side conditions.** `NoCodeSep s`, `NoMultisig s` (no such instruction in the parsed script); `StepOk v s i` (the instruction is not an executed code separator, and a multisig's signatures do not occur as pushes in the current script code), `RunOk`, `EvalOk c v stack script` (along the actual run).
--
--   **Formalization Note.** The published interpreter (`BitcoinScript`, `BitcoinSig.legacyOracle`, `BitcoinVerify.verifyScript`) is exact except for two documented limits: L1 (the script code does not restart after an executed `OP_CODESEPARATOR`) and L10 (`OP_CHECKMULTISIG` deletes only the checked signature). This file is the interpreter without those limits; the theorems state that it agrees with the published one wherever the limits do not bite, and its tests agree with every one of Core's 994 script and transaction vectors at the pinned revision. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Std
import Definitions.Def_BitcoinVerify

namespace BitcoinScriptV2

/-! The legacy (`SigVersion::BASE`) and witness-v0 script interpreter of Bitcoin Core at revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`, revised to close the two documented limits of
`BitcoinScript`/`BitcoinVerify` (`REVIEW.md` L1 and L10):

* **L1** (`EvalScript`, interpreter.cpp:432, 1058–1066): the script code handed to the signature
  checker is `CScript(pbegincodehash, pend)`, the bytes of the executed script from the position
  just after the last *executed* `OP_CODESEPARATOR` (initially the whole script). The published
  model always uses the whole script.
* **L10** (`OP_CHECKMULTISIG`, interpreter.cpp:1149–1159): in `SigVersion::BASE` the pushes of
  *all* `nSigsCount` signatures are `FindAndDelete`d from that script code, in stack order from the
  top, before any signature is checked; the published oracle deletes only the signature it checks.

Design. The interpreter runs over the parsed script paired with byte offsets: `annotate` is the
`GetOp` parse that pairs every instruction with the bytes that follow it (Core's `pc` after reading
it, i.e. `CScript(pc, pend)`). The state `StateV2` carries the published `State` together with
`scriptCode = CScript(pbegincodehash, pend)`. The oracle `OracleV2` receives the script code with the
`FindAndDelete`s already applied: `checkSig scriptCode sig pk` is the two encoding checks followed by
`checker.CheckECDSASignature(sig, pk, scriptCode, sigversion)`; the interpreter itself performs
Core's `FindAndDelete`s (one signature for `OP_CHECKSIG(VERIFY)`, every signature for
`OP_CHECKMULTISIG(VERIFY)`, `SigVersion::BASE` only). Every opcode is executed by the published
`BitcoinScript.execOp` through `BitcoinScript.step`, given a `BitcoinScript.Oracle` whose `checkSig`
is the V2 oracle applied to the right script code (`oracleAt`); only the bookkeeping of
`pbegincodehash` is new. -/

open BitcoinScript (Byte Bytes Instr Script Flags Oracle State allTrue toNum nDefaultMaxNumSize
  OP_CODESEPARATOR OP_CHECKSIG OP_CHECKSIGVERIFY OP_CHECKMULTISIG OP_CHECKMULTISIGVERIFY)
open BitcoinSig (SigVersion SigFlags getOp pushBytes findAndDelete)
open BitcoinSer (Tx)

/-! ### The oracle -/

/-- The primitives the V2 interpreter calls out to. `checkSig scriptCode sig pk` is
`EvalChecksigPreTapscript` *after* its `FindAndDelete` (interpreter.cpp:345–349), equally the body
of the `OP_CHECKMULTISIG` loop (interpreter.cpp:1170–1177): `none` when `CheckSignatureEncoding` or
`CheckPubKeyEncoding` fails the script, otherwise `some` of
`checker.CheckECDSASignature(sig, pk, scriptCode, sigversion)` on the given script code. -/
structure OracleV2 where
  ripemd160 : Bytes → Bytes
  sha1 : Bytes → Bytes
  sha256 : Bytes → Bytes
  hash160 : Bytes → Bytes
  hash256 : Bytes → Bytes
  checkSig : (scriptCode : Bytes) → (sig pk : Bytes) → Option Bool
  checkLockTime : Int → Bool
  checkSequence : Int → Bool

/-- The published oracle with the same hash and lock-time primitives and a `checkSig` that never
answers (it is replaced by `withCode`/`withCodeSig` before any signature opcode runs). -/
def toOracle (o : OracleV2) : Oracle :=
  ⟨o.ripemd160, o.sha1, o.sha256, o.hash160, o.hash256, fun _ _ => none, o.checkLockTime, o.checkSequence⟩

/-- `FindAndDelete(scriptCode, CScript() << sig)` for `SigVersion::BASE`; witness v0 scripts are not
modified (interpreter.cpp:338–343, 1151–1159). -/
def fadSig (v : SigVersion) (sc sig : Bytes) : Bytes :=
  match v with
  | .base => (findAndDelete sc (pushBytes sig)).1
  | .witnessV0 => sc

/-- The `for (int k = 0; k < nSigsCount; k++)` loop of `OP_CHECKMULTISIG` (interpreter.cpp:1152–1159):
every signature's push deleted in turn, from the top of the stack down. -/
def fadAll (v : SigVersion) (sc : Bytes) (sigs : List Bytes) : Bytes := sigs.foldl (fadSig v) sc

/-- The published oracle checking against one fixed script code (the `OP_CHECKMULTISIG` loop, whose
`scriptCode` is computed once before the loop). -/
def withCode (o : OracleV2) (sc : Bytes) : Oracle := { toOracle o with checkSig := o.checkSig sc }

/-- The published oracle for `OP_CHECKSIG(VERIFY)`: `EvalChecksigPreTapscript` on the script code
`sc = CScript(pbegincodehash, pend)`, which deletes the push of the signature being checked first. -/
def withCodeSig (o : OracleV2) (v : SigVersion) (sc : Bytes) : Oracle :=
  { toOracle o with checkSig := fun sig pk => o.checkSig (fadSig v sc sig) sig pk }

/-! ### The signatures of an `OP_CHECKMULTISIG` -/

/-- The `nSigsCount` signatures `stacktop(-isig-k)`, `k = 0 … nSigsCount-1`, of an
`OP_CHECKMULTISIG` executed on this (top-first) stack: the elements below the key count, the keys
and the signature count. (When the counts are out of range or the stack too short, `execOp` fails
before consulting the oracle and this value is irrelevant.) -/
def multisigSigs (stack : List Bytes) : List Bytes :=
  match stack with
  | [] => []
  | nk :: rest =>
    match toNum false nDefaultMaxNumSize nk with
    | none => []
    | some nKeys =>
      match rest.drop nKeys.toNat with
      | [] => []
      | ns :: rest =>
        match toNum false nDefaultMaxNumSize ns with
        | none => []
        | some nSigs => rest.take nSigs.toNat

/-! ### Execution state and steps -/

/-- The published state together with `scriptCode = CScript(pbegincodehash, pend)`. -/
structure StateV2 where
  st : State
  scriptCode : Bytes

/-- The published oracle the instruction `i` is executed with: at `OP_CHECKMULTISIG(VERIFY)` the
checker on the script code with every signature deleted (interpreter.cpp:1149–1177); at every other
instruction `withCodeSig`, which is `EvalChecksigPreTapscript` for `OP_CHECKSIG(VERIFY)`
(interpreter.cpp:1080, 331–349) and is not consulted by any other opcode. -/
def oracleAt (v : SigVersion) (o : OracleV2) (s : StateV2) : Instr → Oracle
  | .op c =>
    if c == OP_CHECKMULTISIG || c == OP_CHECKMULTISIGVERIFY then
      withCode o (fadAll v s.scriptCode (multisigSigs s.st.stack))
    else withCodeSig o v s.scriptCode
  | .push _ => withCodeSig o v s.scriptCode

/-- One iteration of the `for (; pc < pend; …)` loop of `EvalScript` on the instruction `i` followed
by the bytes `r` (`pc` after `GetOp`): the published `step` with the oracle `oracleAt`, and
`pbegincodehash = pc` when an `OP_CODESEPARATOR` is executed (interpreter.cpp:1058–1066; the opcode
is executed iff `fExec`, since it lies outside `OP_IF … OP_ENDIF`). -/
def stepV2 (f : Flags) (v : SigVersion) (o : OracleV2) (s : StateV2) : Instr × Bytes → Option StateV2
  | (i, r) =>
    (BitcoinScript.step f (oracleAt v o s i) s.st i).map fun st =>
      ⟨st, if i = .op OP_CODESEPARATOR ∧ allTrue s.st.vfExec then r else s.scriptCode⟩

/-- The loop over the annotated instructions, followed by the unbalanced-conditional check. -/
def runV2 (f : Flags) (v : SigVersion) (o : OracleV2) : StateV2 → List (Instr × Bytes) → Option StateV2
  | s, [] => if s.st.vfExec.isEmpty then some s else none
  | s, x :: rest =>
    match stepV2 f v o s x with
    | none => none
    | some s' => runV2 f v o s' rest

/-! ### Byte-level scripts with positions -/

/-- The `GetOp` parse pairing every instruction with the bytes after it: for `annotate script =
some l`, `(i, r) ∈ l` means `script = pre ++ bytes-of-i ++ r`, so `r` is `CScript(pc, pend)` once
`i` has been read. `none` on a malformed push, as `BitcoinSig.parseScript`. -/
def annotateAux : Nat → Bytes → Option (List (Instr × Bytes))
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, s =>
    match getOp s with
    | none => none
    | some (i, r) =>
      match annotateAux fuel r with
      | none => none
      | some l => some ((i, r) :: l)

def annotate (s : Bytes) : Option (List (Instr × Bytes)) := annotateAux s.length s

/-- `EvalScript(stack, script, flags, checker, sigversion)` for `BASE`/`WITNESS_V0` on a byte script
(without the `MAX_SCRIPT_SIZE` test): the resulting main stack. `pbegincodehash` starts at
`script.begin()`. -/
def evalScriptV2 (f : Flags) (v : SigVersion) (o : OracleV2) (stack : List Bytes) (script : Bytes) :
    Option (List Bytes) :=
  match annotate script with
  | none => none
  | some l => (runV2 f v o ⟨State.initial stack, script⟩ l).map fun s => s.st.stack

/-! ### The concrete oracle and `VerifyScript` -/

/-- The concrete V2 oracle: Core's hashes, the encoding checks and
`GenericTransactionSignatureChecker::CheckECDSASignature` on the script code the interpreter
supplies, and the lock-time checks. -/
def legacyOracleV2 (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int) (v : SigVersion) : OracleV2 where
  ripemd160 := BitcoinSer.ripemd160
  sha1 := BitcoinSer.sha1
  sha256 := BitcoinSer.sha256
  hash160 := BitcoinSer.hash160
  hash256 := BitcoinSer.hash256
  checkSig := fun scriptCode sig pk =>
    if !BitcoinSig.checkSignatureEncoding f sig ∨ !BitcoinSig.checkPubKeyEncoding f v pk then none
    else some (BitcoinSig.checkECDSASignature tx nIn amount v sig pk scriptCode)
  checkLockTime := BitcoinSig.checkLockTime tx nIn
  checkSequence := BitcoinSig.checkSequence tx nIn

open BitcoinVerify (Ctx MAX_SCRIPT_SIZE scriptFlagsOf sigFlagsOf topTrue isWitnessProgram
  isPayToScriptHash isPushOnly isPayToAnchor p2wpkhExec TaprootHandler
  WITNESS_V0_SCRIPTHASH_SIZE WITNESS_V0_KEYHASH_SIZE WITNESS_V1_TAPROOT_SIZE)

/-- `EvalScript` on a byte-level script with the concrete oracle: the `MAX_SCRIPT_SIZE` test, then
`evalScriptV2`. Mirrors `BitcoinVerify.evalBytes`. -/
def evalBytesV2 (c : Ctx) (v : SigVersion) (stack : List Bytes) (script : Bytes) : Option (List Bytes) :=
  if MAX_SCRIPT_SIZE < script.length then none
  else evalScriptV2 (scriptFlagsOf c.flags) v (legacyOracleV2 (sigFlagsOf c.flags) c.tx c.nIn c.amount v) stack script

/-- `ExecuteWitnessScript` for witness version 0 with the V2 evaluator. -/
def executeWitnessScriptV0V2 (c : Ctx) (stack : List Bytes) (exec : Bytes) : Bool :=
  if stack.any (fun e => BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE < e.length) then false
  else match evalBytesV2 c .witnessV0 stack exec with
    | none => false
    | some st => decide (st.length = 1) && topTrue st

/-- `VerifyWitnessProgram` with the V2 evaluator for version 0; the Taproot branch is unchanged. -/
def verifyWitnessProgramV2 (tap : TaprootHandler) (c : Ctx) (witness : List Bytes) (version : Nat)
    (program : Bytes) (isP2sh : Bool) : Bool :=
  if version = 0 then
    if program.length = WITNESS_V0_SCRIPTHASH_SIZE then
      match witness.getLast? with
      | none => false
      | some script =>
        if BitcoinSer.sha256 script ≠ program then false
        else executeWitnessScriptV0V2 c witness.dropLast.reverse script
    else if program.length = WITNESS_V0_KEYHASH_SIZE then
      if witness.length ≠ 2 then false
      else executeWitnessScriptV0V2 c witness.reverse (p2wpkhExec program)
    else false
  else if version = 1 ∧ program.length = WITNESS_V1_TAPROOT_SIZE ∧ !isP2sh then
    if !c.flags.taproot then true else tap c witness program
  else if !isP2sh && isPayToAnchor version program then true
  else true

/-- `VerifyScript` with the V2 evaluator on the legacy and witness-v0 paths; mirrors
`BitcoinVerify.verifyScript` line by line. -/
def verifyScriptV2 (tap : TaprootHandler) (c : Ctx) (scriptSig scriptPubKey : Bytes) (witness : List Bytes) : Bool :=
  match evalBytesV2 c .base [] scriptSig with
  | none => false
  | some stackSig =>
    match evalBytesV2 c .base stackSig scriptPubKey with
    | none => false
    | some stack =>
      if !topTrue stack then false
      else
        let native : Option Bool :=
          if c.flags.witness then
            match isWitnessProgram scriptPubKey with
            | some (version, program) =>
              if scriptSig ≠ [] then some false
              else some (verifyWitnessProgramV2 tap c witness version program false)
            | none => none
          else none
        match native with
        | some false => false
        | some true => true
        | none =>
          if c.flags.p2sh && isPayToScriptHash scriptPubKey then
            if !isPushOnly scriptSig then false
            else
              match stackSig with
              | [] => false
              | redeem :: rest =>
                match evalBytesV2 c .base rest redeem with
                | none => false
                | some stack2 =>
                  if !topTrue stack2 then false
                  else
                    if c.flags.witness then
                      match isWitnessProgram redeem with
                      | some (version, program) =>
                        if scriptSig ≠ BitcoinSig.pushBytes redeem then false
                        else verifyWitnessProgramV2 tap c witness version program true
                      | none => if c.flags.witness && !witness.isEmpty then false else true
                    else true
          else if c.flags.witness && !witness.isEmpty then false
          else true

/-! ### The side conditions of the agreement theorems -/

/-- The script contains no `OP_CODESEPARATOR` instruction. -/
def NoCodeSep (s : Script) : Prop := Instr.op OP_CODESEPARATOR ∉ s

/-- The script contains no `OP_CHECKMULTISIG(VERIFY)` instruction. -/
def NoMultisig (s : Script) : Prop := Instr.op OP_CHECKMULTISIG ∉ s ∧ Instr.op OP_CHECKMULTISIGVERIFY ∉ s

/-- The instruction `i`, executed from the state `s`, is outside the two limits: it is not an
executed `OP_CODESEPARATOR` (L1), and if it is an executed `OP_CHECKMULTISIG(VERIFY)` then no
signature's push occurs in the script code, so that every `FindAndDelete` is the identity (L10;
vacuous for witness v0, where there is no `FindAndDelete`). -/
def StepOk (v : SigVersion) (s : StateV2) : Instr → Prop
  | .push _ => True
  | .op c => allTrue s.st.vfExec = true →
      c ≠ OP_CODESEPARATOR ∧
      ((c = OP_CHECKMULTISIG ∨ c = OP_CHECKMULTISIGVERIFY) →
        ∀ sig ∈ multisigSigs s.st.stack, fadSig v s.scriptCode sig = s.scriptCode)

/-- Every step of the V2 run from `s` over `l` (as far as it gets) satisfies `StepOk`. -/
def RunOk (f : Flags) (v : SigVersion) (o : OracleV2) : StateV2 → List (Instr × Bytes) → Prop
  | _, [] => True
  | s, x :: rest => StepOk v s x.1 ∧ ∀ s', stepV2 f v o s x = some s' → RunOk f v o s' rest

/-- The V2 evaluation of `script` from `stack` in the context `c` stays outside the two limits. -/
def EvalOk (c : Ctx) (v : SigVersion) (stack : List Bytes) (script : Bytes) : Prop :=
  ∀ l, annotate script = some l →
    RunOk (scriptFlagsOf c.flags) v (legacyOracleV2 (sigFlagsOf c.flags) c.tx c.nIn c.amount v)
      ⟨State.initial stack, script⟩ l

end BitcoinScriptV2


