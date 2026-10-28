-- Prove2me | Definitions.Def_BitcoinVerify
-- name    : BitcoinVerify
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-26T15:04:47.097125+00:00
-- url     : https://prove2.me/theorems/4dbde1d9-b777-46dd-b4bc-24095f135654
-- title:
--   VerifyScript: P2SH, native and wrapped SegWit v0, unknown witness versions, and the taproot hand-off
-- statement:
--   **Context and flags.** A `Ctx` is the spending transaction, the input index, the amount spent and the consensus flag set (`BitcoinActivation.ScriptFlags`, the output of `GetBlockScriptFlags`); `scriptFlagsOf` and `sigFlagsOf` project the interpreter and signature-layer flags (`DERSIG` is the only signature flag on mainnet). $\mathrm{MAX\_SCRIPT\_SIZE} = 10{,}000$.
--
--   **Byte-level evaluation.** `evalBytes ctx v stack script` is `EvalScript` on a byte string: the size test, the `GetOp` parse (`none` on a malformed push), and the Script mission's interpreter with the concrete oracle of the signature mission for signature version `v` and this script code.
--
--   **Predicates.** `isPayToScriptHash` is `CScript::IsPayToScriptHash` (23 bytes `a9 14 … 87`); `isWitnessProgram` is `IsWitnessProgram` (`OP_0`/`OP_1..16` then one push of 2–40 bytes, nothing else; returns the version and program); `isPushOnly` is `IsPushOnly` (every instruction parses and has opcode at most `OP_16`); `isPayToAnchor` is the version-1 two-byte `4e73` program; `topTrue` is `CastToBool` of the top, false on an empty stack.
--
--   **Witness execution.** `executeWitnessScriptV0` is `ExecuteWitnessScript` for version 0: every element within 520 bytes, the script run under `WITNESS_V0`, exactly one element left and it true. `verifyWitnessProgram` is `VerifyWitnessProgram`: version 0 with a 32-byte program is P2WSH (last witness element is the script, its SHA-256 must equal the program, the rest is the initial stack), with a 20-byte program is P2WPKH (exactly two elements, the implied `DUP HASH160 <program> EQUALVERIFY CHECKSIG`), other lengths fail; version 1 with a 32-byte program outside P2SH is Taproot, delegated to the `TaprootHandler` parameter when the `TAPROOT` flag is set and accepted otherwise; pay-to-anchor and every other version/size combination succeed. Witness stacks are in `CScriptWitness` order (last element on top), reversed into the interpreter's top-first stacks.
--
--   **`verifyScript`** is `VerifyScript` with the consensus flags: the scriptSig and then the output script on the same stack, a true top; with `WITNESS`, a witness-program output requires an empty scriptSig and runs the program; with `P2SH`, a P2SH output requires a push-only scriptSig, restores the scriptSig's stack, pops the serialized redeem script and runs it, requires a true top, and, with `WITNESS`, a witness-program redeem script requires the scriptSig to be exactly its single push and runs the program as P2SH-wrapped; finally, with `WITNESS`, a non-empty witness that nothing consumed fails. `SIGPUSHONLY` and `CLEANSTACK` are policy and off.
--
--   **Templates.** `p2shBytes h`, `witnessBytes v program`, `pushesBytes` (a push-only scriptSig), `p2wpkhExec`.
--
--   **Formalization Note.** Policy flags are off; the Taproot branch is a parameter supplied by the Taproot development; the oracle's script code is the executed script, exact for scripts without `OP_CODESEPARATOR`. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, VerifyWitnessProgram, ExecuteWitnessScript, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScript::IsPayToScriptHash, IsWitnessProgram, IsPushOnly, IsPayToAnchor, DecodeOP_N, src/script/script.cpp and script.h; MAX_SCRIPT_SIZE, WITNESS_V0_SCRIPTHASH_SIZE, WITNESS_V0_KEYHASH_SIZE, WITNESS_V1_TAPROOT_SIZE; BIP16, BIP141, BIP143 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Std
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinActivation

namespace BitcoinVerify

/-! Transcription of `VerifyScript`, `VerifyWitnessProgram` (witness version 0, unknown versions,
pay-to-anchor) and `ExecuteWitnessScript` of `script/interpreter.cpp`, and `IsPayToScriptHash`,
`IsWitnessProgram`, `IsPushOnly`, `IsPayToAnchor` of `script/script.cpp`, at Bitcoin Core revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`, with the mainnet consensus flag set of
`GetBlockScriptFlags` (`BitcoinActivation.ScriptFlags`). The Taproot (version 1, 32-byte, non-P2SH)
branch is a parameter `taproot`, supplied by the Taproot development. -/

open BitcoinSer (Byte Bytes Tx)
open BitcoinSig (SigVersion)

/-- `MAX_SCRIPT_SIZE = 10000`. -/
def MAX_SCRIPT_SIZE : Nat := 10000
def WITNESS_V0_SCRIPTHASH_SIZE : Nat := 32
def WITNESS_V0_KEYHASH_SIZE : Nat := 20
def WITNESS_V1_TAPROOT_SIZE : Nat := 32

/-- The interpreter flags carried by the consensus flag set. -/
def scriptFlagsOf (f : BitcoinActivation.ScriptFlags) : BitcoinScript.Flags := ⟨f.cltv, f.csv, f.nulldummy⟩
/-- The signature-layer flags: `DERSIG` is the only consensus one; the policy flags are off. -/
def sigFlagsOf (f : BitcoinActivation.ScriptFlags) : BitcoinSig.SigFlags := ⟨f.dersig, false, false, false⟩

/-- The context of one script verification: the spending transaction, the input index and the amount
spent (`-1` where unknown, as for legacy inputs validated without amounts). -/
structure Ctx where
  flags : BitcoinActivation.ScriptFlags
  tx : Tx
  nIn : Nat
  amount : Int

/-- `EvalScript(stack, script, flags, checker, sigversion)` on a byte-level script: the
`MAX_SCRIPT_SIZE` test, the `GetOp` parse, and the Script mission's interpreter with the concrete
oracle for this script code. `stack` is top-first. -/
def evalBytes (c : Ctx) (v : SigVersion) (stack : List Bytes) (script : Bytes) : Option (List Bytes) :=
  if MAX_SCRIPT_SIZE < script.length then none
  else match BitcoinSig.parseScript script with
    | none => none
    | some s =>
      BitcoinScript.evalScript (scriptFlagsOf c.flags)
        (BitcoinSig.legacyOracle (sigFlagsOf c.flags) c.tx c.nIn c.amount v script) stack s

/-- `CScript::IsPayToScriptHash`: `OP_HASH160 <20 bytes> OP_EQUAL`, 23 bytes. -/
def isPayToScriptHash (s : Bytes) : Bool :=
  decide (s.length = 23) && decide ((s.getD 0 0).toNat = 0xa9) && decide ((s.getD 1 0).toNat = 0x14) &&
  decide ((s.getD 22 0).toNat = 0x87)

/-- `DecodeOP_N`. -/
def decodeOpN (b : Nat) : Nat := if b = 0 then 0 else b - 0x50

/-- `CScript::IsWitnessProgram`: `OP_0`/`OP_1..OP_16`, a direct push of 2..40 bytes, nothing else. -/
def isWitnessProgram (s : Bytes) : Option (Nat × Bytes) :=
  if s.length < 4 ∨ 42 < s.length then none
  else
    let b0 := (s.getD 0 0).toNat
    if b0 ≠ 0 ∧ (b0 < 0x51 ∨ 0x60 < b0) then none
    else if (s.getD 1 0).toNat + 2 = s.length then some (decodeOpN b0, s.drop 2)
    else none

/-- `CScript::IsPushOnly`: every instruction parses and is a push or `OP_RESERVED`/`OP_1NEGATE`/`OP_n`
(opcode at most `OP_16`). -/
def isPushOnlyAux : Nat → Bytes → Bool
  | _, [] => true
  | 0, _ => false
  | fuel + 1, s =>
    match BitcoinSig.getOp s with
    | none => false
    | some (.push _, r) => isPushOnlyAux fuel r
    | some (.op c, r) => if BitcoinScript.OP_16 < c then false else isPushOnlyAux fuel r

def isPushOnly (s : Bytes) : Bool := isPushOnlyAux s.length s

/-- `CScript::IsPayToAnchor(version, program)`. -/
def isPayToAnchor (version : Nat) (program : Bytes) : Bool :=
  decide (version = 1) && decide (program = [0x4e, 0x73])

/-- `CastToBool` of the top of a top-first stack; an empty stack is `false` (`SCRIPT_ERR_EVAL_FALSE`). -/
def topTrue (stack : List Bytes) : Bool :=
  match stack with
  | [] => false
  | top :: _ => BitcoinScript.castToBool top

/-- `ExecuteWitnessScript` for witness version 0: every witness element within
`MAX_SCRIPT_ELEMENT_SIZE`, the script run with `SigVersion::WITNESS_V0`, exactly one element left,
and it true. `stack` is top-first. -/
def executeWitnessScriptV0 (c : Ctx) (stack : List Bytes) (exec : Bytes) : Bool :=
  if stack.any (fun e => BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE < e.length) then false
  else match evalBytes c .witnessV0 stack exec with
    | none => false
    | some st => decide (st.length = 1) && topTrue st

/-- The implied P2WPKH script `OP_DUP OP_HASH160 <program> OP_EQUALVERIFY OP_CHECKSIG`. -/
def p2wpkhExec (program : Bytes) : Bytes := BitcoinSig.p2pkhBytes program

/-- A Taproot handler: given the witness stack (in `CScriptWitness` order, last element on top)
and the 32-byte program, the verdict of the BIP341 branch. -/
abbrev TaprootHandler := Ctx → List Bytes → Bytes → Bool

/-- `VerifyWitnessProgram(witness, witversion, program, flags, checker, is_p2sh)`. The witness
stack is in `CScriptWitness` order (last element on top). -/
def verifyWitnessProgram (tap : TaprootHandler) (c : Ctx) (witness : List Bytes) (version : Nat)
    (program : Bytes) (isP2sh : Bool) : Bool :=
  if version = 0 then
    if program.length = WITNESS_V0_SCRIPTHASH_SIZE then
      -- P2WSH: the last element is the script, its SHA-256 must be the program
      match witness.getLast? with
      | none => false
      | some script =>
        if BitcoinSer.sha256 script ≠ program then false
        else executeWitnessScriptV0 c witness.dropLast.reverse script
    else if program.length = WITNESS_V0_KEYHASH_SIZE then
      if witness.length ≠ 2 then false
      else executeWitnessScriptV0 c witness.reverse (p2wpkhExec program)
    else false
  else if version = 1 ∧ program.length = WITNESS_V1_TAPROOT_SIZE ∧ !isP2sh then
    if !c.flags.taproot then true else tap c witness program
  else if !isP2sh && isPayToAnchor version program then true
  else true

/-- `VerifyScript(scriptSig, scriptPubKey, witness, flags, checker)` with the consensus flags
(`SIGPUSHONLY` and `CLEANSTACK` are policy and off). -/
def verifyScript (tap : TaprootHandler) (c : Ctx) (scriptSig scriptPubKey : Bytes) (witness : List Bytes) : Bool :=
  match evalBytes c .base [] scriptSig with
  | none => false
  | some stackSig =>
    match evalBytes c .base stackSig scriptPubKey with
    | none => false
    | some stack =>
      if !topTrue stack then false
      else
        -- bare witness programs
        let native : Option Bool :=
          if c.flags.witness then
            match isWitnessProgram scriptPubKey with
            | some (version, program) =>
              if scriptSig ≠ [] then some false
              else some (verifyWitnessProgram tap c witness version program false)
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
                match evalBytes c .base rest redeem with
                | none => false
                | some stack2 =>
                  if !topTrue stack2 then false
                  else
                    if c.flags.witness then
                      match isWitnessProgram redeem with
                      | some (version, program) =>
                        if scriptSig ≠ BitcoinSig.pushBytes redeem then false
                        else verifyWitnessProgram tap c witness version program true
                      | none => if c.flags.witness && !witness.isEmpty then false else true
                    else true
          else if c.flags.witness && !witness.isEmpty then false
          else true

/-- The P2SH output script `OP_HASH160 <h> OP_EQUAL`. -/
def p2shBytes (h : Bytes) : Bytes := [0xa9] ++ BitcoinSig.pushBytes h ++ [0x87]

/-- A witness output script `OP_n <program>`. -/
def witnessBytes (version : Nat) (program : Bytes) : Bytes :=
  BitVec.ofNat 8 (if version = 0 then 0 else 0x50 + version) :: BitcoinSig.pushBytes program

/-- A push-only scriptSig: the canonical pushes of the given elements, in order. -/
def pushesBytes (ps : List Bytes) : Bytes := ps.flatMap BitcoinSig.pushBytes

end BitcoinVerify


