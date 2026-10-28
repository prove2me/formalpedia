-- Prove2me | Definitions.Def_BitcoinTaproot
-- name    : BitcoinTaproot
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-26T16:34:12.460167+00:00
-- url     : https://prove2.me/theorems/b7c3e261-301b-42a1-a275-cfd955f1a134
-- title:
--   Taproot and Tapscript: the version-1 witness branch, BIP341 signature hash, commitment check, and the Tapscript interpreter rules
-- statement:
--   **Constants.** `TAPROOT_LEAF_MASK` = 0xfe, `TAPROOT_LEAF_TAPSCRIPT` = 0xc0, control-block sizes 33 + 32·k for $k \le 128$, `ANNEX_TAG` = 0x50, `VALIDATION_WEIGHT_OFFSET` = 50, `VALIDATION_WEIGHT_PER_SIGOP_PASSED` = 50, `SIGHASH_DEFAULT` = 0, `OP_CHECKSIGADD` = 0xba.
--
--   **Hashes and the tweak.** `tagged t m` is the BIP340 tagged hash $\mathrm{SHA256}(\mathrm{SHA256}(t)\,\|\,\mathrm{SHA256}(t)\,\|\,m)$. `tapleafHash v s` = `TapLeaf`(v ‖ compactSize(|s|) ‖ s); `tapbranchHash a b` = `TapBranch` of the two children in lexicographic order (`lexLt` is `std::lexicographical_compare`); `controlNodes` cuts the 32-byte path nodes after the 33-byte base; `taprootMerkleRoot control leaf` folds `tapbranchHash` over them from the leaf; `tapTweakHash p r` = `TapTweak`(p ‖ r). `xonlyTweakAddCheck q parity P t` is `secp256k1_xonly_pubkey_tweak_add_check`: $t < n$, $Q = P + tG \ne \mathcal{O}$, $x(Q)$ is the 32-byte key `q` and the parity of $y(Q)$ is `parity`; `checkTapTweak` lifts the internal key with the signature mission's `liftX` first; `verifyTaprootCommitment control program leafHash` is `VerifyTaprootCommitment` (parity from bit 0 of the control byte, internal key bytes 1–32, root from the path).
--
--   **BIP341 signature hash.** `sigHashSchnorr tx spent inPos hashType tapscript ed` is `SignatureHashSchnorr` with `ExecData` (annex presence and hash, tapleaf hash, code-separator position): `none` for a hash type outside $\{0,1,2,3,0x81,0x82,0x83\}$ and for `SIGHASH_SINGLE` without a matching output; otherwise the `TapSighash` tagged hash of the epoch byte, hash type, version, locktime, the four precomputed hashes unless `ANYONECANPAY`, the outputs hash for `ALL`, the spend-type byte, the input (index, or outpoint ‖ spent output ‖ sequence), the annex hash, the single-output hash and the Tapscript extension. `spent` lists the spent outputs, one per input.
--
--   **Schnorr check.** `checkSchnorrSignature tx spent nIn sig q tapscript ed` is `CheckSchnorrSignature`: 64 bytes (`SIGHASH_DEFAULT`) or 65 bytes whose last byte is a non-zero hash type, then BIP340 `schnorrVerify` of the signature mission over the BIP341 hash.
--
--   **Tapscript (BIP342).** `isOpSuccess` is `IsOpSuccess`; `opSuccessScan` is the pre-scan of `ExecuteWitnessScript` (a malformed push before any success opcode fails). `TapCtx` carries the interpreter flags, transaction, spent outputs and input index; `tapOracle` supplies the hash and locktime oracles of the Script mission (its `checkSig` is never consulted). `TapState` is the interpreter state plus the remaining validation weight, the code-separator position and the opcode position. `evalChecksigTapscript` is `EvalChecksigTapscript`: a non-empty signature costs 50 weight and fails on a negative budget, an empty key fails, a 32-byte key runs the Schnorr check, other key lengths succeed (upgradable). `tapExecOp` is one executed opcode under `TAPSCRIPT`: `MINIMALIF` on `OP_IF`/`OP_NOTIF`, `OP_CHECKSIG(VERIFY)` and `OP_CHECKSIGADD` via `evalChecksigTapscript`, `OP_CHECKMULTISIG(VERIFY)` fail, `OP_CODESEPARATOR` records the opcode position, everything else is the Script mission's `execOp`. `tapStep`/`tapRun` are the loop (no operation count, push-size and stack-size limits, conditional skipping, opcode position); `executeTapscript c ed stack script weight` is `ExecuteWitnessScript` under `TAPSCRIPT` (scan, initial limits, run, exactly one true element).
--
--   **The version-1 branch.** `hasAnnex` (two or more elements and a last element starting with 0x50), `witnessSerializedSize`; `taprootHandler spent : BitcoinVerify.TaprootHandler` is the version-1 branch of `VerifyWitnessProgram`: an empty witness fails; one element after the annex is the key path (Schnorr check of the output key, no tapleaf, code separator 0xFFFFFFFF); otherwise the control block and script are popped, the control size is checked, the leaf version is masked, the commitment verified, and leaf version 0xc0 runs Tapscript on the remaining elements with the weight budget $|\mathrm{ser}(\text{witness})| + 50$, other leaf versions succeed. `verifyScriptFull spent` is the complete `VerifyScript` with this handler; `p2trBytes q` = `OP_1 <q>`.
--
--   **Formalization Note.** Policy flags (`DISCOURAGE_UPGRADABLE_TAPROOT_VERSION`, `DISCOURAGE_UPGRADABLE_PUBKEYTYPE`, `DISCOURAGE_OP_SUCCESS`) are off, as in block validation. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Std
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinVerify

namespace BitcoinTaproot

/-! Transcription of Bitcoin Core's Taproot and Tapscript validation at revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`: the version-1 branch of `VerifyWitnessProgram` (annex,
key path, script path), `ComputeTapleafHash`, `ComputeTapbranchHash`, `ComputeTaprootMerkleRoot`,
`VerifyTaprootCommitment` (`script/interpreter.cpp`), `XOnlyPubKey::CheckTapTweak` and
`ComputeTapTweakHash` (`pubkey.cpp`) with `secp256k1_xonly_pubkey_tweak_add_check`,
`SignatureHashSchnorr` (BIP341), `CheckSchnorrSignature`, `EvalChecksigTapscript`, the Tapscript
rules of `EvalScript` and `ExecuteWitnessScript` (BIP342: `OP_SUCCESSx`, `MINIMALIF`,
`OP_CHECKSIGADD`, no `OP_CHECKMULTISIG`, the validation-weight budget, `OP_CODESEPARATOR`
positions, no operation count), and `IsOpSuccess` (`script/script.cpp`). -/

open BitcoinSer (Byte Bytes Tx TxIn TxOut)
open BitcoinScript (Instr Script State Flags Oracle)

def TAPROOT_LEAF_MASK : Nat := 0xfe
def TAPROOT_LEAF_TAPSCRIPT : Nat := 0xc0
def TAPROOT_CONTROL_BASE_SIZE : Nat := 33
def TAPROOT_CONTROL_NODE_SIZE : Nat := 32
def TAPROOT_CONTROL_MAX_NODE_COUNT : Nat := 128
def TAPROOT_CONTROL_MAX_SIZE : Nat := TAPROOT_CONTROL_BASE_SIZE + TAPROOT_CONTROL_NODE_SIZE * TAPROOT_CONTROL_MAX_NODE_COUNT
def ANNEX_TAG : Nat := 0x50
def VALIDATION_WEIGHT_OFFSET : Int := 50
def VALIDATION_WEIGHT_PER_SIGOP_PASSED : Int := 50
def SIGHASH_DEFAULT : Nat := 0
/-- `OP_CHECKSIGADD = 0xba` (BIP342). -/
def OP_CHECKSIGADD : Byte := 0xba

/-! ### Tagged hashes, leaves, branches, the tweak -/

def tagged (tag : String) (m : Bytes) : Bytes := BitcoinSig.taggedHash (BitcoinSig.ascii tag) m

/-- `ComputeTapleafHash(leaf_version, script)`. -/
def tapleafHash (leafVersion : Byte) (script : Bytes) : Bytes :=
  tagged "TapLeaf" ([leafVersion] ++ BitcoinSer.writeCompactSize script.length ++ script)

/-- `std::lexicographical_compare` on byte strings. -/
def lexLt : Bytes → Bytes → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a.toNat < b.toNat then true else if b.toNat < a.toNat then false else lexLt as bs

/-- `ComputeTapbranchHash(a, b)`: the lexicographically smaller first. -/
def tapbranchHash (a b : Bytes) : Bytes :=
  tagged "TapBranch" (if lexLt a b then a ++ b else b ++ a)

/-- The path nodes of a control block: 32-byte chunks after the 33-byte base. -/
def controlNodes (control : Bytes) : List Bytes :=
  let rec go : Nat → Bytes → List Bytes
    | 0, _ => []
    | k + 1, s => s.take TAPROOT_CONTROL_NODE_SIZE :: go k (s.drop TAPROOT_CONTROL_NODE_SIZE)
  go ((control.length - TAPROOT_CONTROL_BASE_SIZE) / TAPROOT_CONTROL_NODE_SIZE) (control.drop TAPROOT_CONTROL_BASE_SIZE)

/-- `ComputeTaprootMerkleRoot(control, tapleaf_hash)`. -/
def taprootMerkleRoot (control : Bytes) (leafHash : Bytes) : Bytes :=
  (controlNodes control).foldl tapbranchHash leafHash

/-- `XOnlyPubKey::ComputeTapTweakHash(&merkle_root)`. -/
def tapTweakHash (internal32 merkleRoot : Bytes) : Bytes := tagged "TapTweak" (internal32 ++ merkleRoot)

/-- The 32-byte big-endian encoding of a coordinate. -/
def be32 (x : Nat) : Bytes := BitcoinSer.beBytes 32 x

/-- `secp256k1_xonly_pubkey_tweak_add_check(output32, parity, internal, tweak32)`: with `P` the
even-`y` point of the internal key and `t` the tweak scalar (below `n`), `Q = P + tG` is not infinity,
its abscissa is `output32` and the parity of its ordinate is `parity`. -/
def xonlyTweakAddCheck (output32 : Bytes) (parity : Bool) (P : Nat × Nat) (tweak32 : Bytes) : Bool :=
  let t := BitcoinSig.beVal tweak32
  if BitcoinSig.n ≤ t then false
  else match BitcoinSig.padd (some P) (BitcoinSig.pmul t BitcoinSig.G) with
    | none => false
    | some (qx, qy) => decide (be32 qx = output32) && decide ((qy % 2 = 1) = parity)

/-- `XOnlyPubKey::CheckTapTweak(internal, merkle_root, parity)` on the output key `q`. -/
def checkTapTweak (q internal32 merkleRoot : Bytes) (parity : Bool) : Bool :=
  match BitcoinSig.liftX (BitcoinSig.beVal internal32) with
  | none => false
  | some P => xonlyTweakAddCheck q parity P (tapTweakHash internal32 merkleRoot)

/-- `VerifyTaprootCommitment(control, program, tapleaf_hash)`. -/
def verifyTaprootCommitment (control program leafHash : Bytes) : Bool :=
  checkTapTweak program ((control.drop 1).take 32) (taprootMerkleRoot control leafHash)
    (decide ((control.getD 0 0).toNat % 2 = 1))

/-! ### The BIP341 signature hash -/

/-- `ScriptExecutionData` as far as the signature hash reads it. -/
structure ExecData where
  annexPresent : Bool
  annexHash : Bytes
  tapleafHash : Bytes
  codeseparatorPos : Nat
  deriving Repr

/-- `SignatureHashSchnorr(tx, in_pos, hash_type, sigversion, cache)`: `none` where it returns `false`
(an undefined hash type, or `SIGHASH_SINGLE` without a matching output). `spent` lists the outputs
being spent, one per input. -/
def sigHashSchnorr (tx : Tx) (spent : List TxOut) (inPos : Nat) (hashType : Nat) (tapscript : Bool)
    (ed : ExecData) : Option Bytes :=
  if ¬ (hashType ≤ 3 ∨ (0x81 ≤ hashType ∧ hashType ≤ 0x83)) then none
  else
    let outputType := if hashType = SIGHASH_DEFAULT then BitcoinSig.SIGHASH_ALL else hashType &&& 3
    let inputType := hashType &&& 0x80
    let extFlag : Nat := if tapscript then 1 else 0
    let spendType : Nat := extFlag * 2 + (if ed.annexPresent then 1 else 0)
    let dfltIn : TxIn := ⟨⟨[], 0⟩, [], 0, []⟩
    let i := tx.vin.getD inPos dfltIn
    let single? : Option Bytes :=
      if outputType = BitcoinSig.SIGHASH_SINGLE then
        if tx.vout.length ≤ inPos then none
        else some (BitcoinSer.sha256 (BitcoinSer.serTxOut (tx.vout.getD inPos ⟨-1, []⟩)))
      else some []
    match single? with
    | none => none
    | some singleOut =>
      some (tagged "TapSighash" (
        [0, BitVec.ofNat 8 hashType] ++ BitcoinSer.ser32 tx.version ++ BitcoinSer.ser32 tx.nLockTime ++
        (if inputType ≠ BitcoinSig.SIGHASH_ANYONECANPAY then
          BitcoinSer.sha256 (tx.vin.flatMap fun i => BitcoinSer.serOutPoint i.prevout) ++
          BitcoinSer.sha256 (spent.flatMap fun o => BitcoinSer.serInt64 o.nValue) ++
          BitcoinSer.sha256 (spent.flatMap fun o => BitcoinSer.serBytes o.scriptPubKey) ++
          BitcoinSer.sha256 (tx.vin.flatMap fun i => BitcoinSer.ser32 i.nSequence)
         else []) ++
        (if outputType = BitcoinSig.SIGHASH_ALL then BitcoinSer.sha256 (tx.vout.flatMap BitcoinSer.serTxOut) else []) ++
        [BitVec.ofNat 8 spendType] ++
        (if inputType = BitcoinSig.SIGHASH_ANYONECANPAY then
          BitcoinSer.serOutPoint i.prevout ++ BitcoinSer.serTxOut (spent.getD inPos ⟨-1, []⟩) ++ BitcoinSer.ser32 i.nSequence
         else BitcoinSer.ser32 inPos) ++
        (if ed.annexPresent then ed.annexHash else []) ++
        singleOut ++
        (if tapscript then ed.tapleafHash ++ [0] ++ BitcoinSer.ser32 ed.codeseparatorPos else [])))

/-- `CheckSchnorrSignature(sig, pubkey, sigversion, execdata)`: 64 or 65 bytes, an explicit hash
type must not be `0`, the BIP341 hash, then BIP340 verification. `false` is a script error. -/
def checkSchnorrSignature (tx : Tx) (spent : List TxOut) (nIn : Nat) (sig pubkey32 : Bytes) (tapscript : Bool)
    (ed : ExecData) : Bool :=
  if sig.length ≠ 64 ∧ sig.length ≠ 65 then false
  else
    let hashType : Nat := if sig.length = 65 then (sig.getLast?.getD 0).toNat else SIGHASH_DEFAULT
    let sig' := if sig.length = 65 then sig.dropLast else sig
    if sig.length = 65 ∧ hashType = SIGHASH_DEFAULT then false
    else match sigHashSchnorr tx spent nIn hashType tapscript ed with
      | none => false
      | some h => BitcoinSig.schnorrVerify pubkey32 h sig'

/-! ### Tapscript (BIP342) -/

/-- `IsOpSuccess`. -/
def isOpSuccess (c : Nat) : Bool :=
  decide (c = 80 ∨ c = 98 ∨ (126 ≤ c ∧ c ≤ 129) ∨ (131 ≤ c ∧ c ≤ 134) ∨ (137 ≤ c ∧ c ≤ 138) ∨
    (141 ≤ c ∧ c ≤ 142) ∨ (149 ≤ c ∧ c ≤ 153) ∨ (187 ≤ c ∧ c ≤ 254))

/-- The `OP_SUCCESSx` pre-scan of `ExecuteWitnessScript`: `some true` when a success opcode is
reached, `some false` when the whole script parses without one, `none` on a malformed push first. -/
def opSuccessScan : Nat → Bytes → Option Bool
  | _, [] => some false
  | 0, _ => none
  | fuel + 1, s =>
    match BitcoinSig.getOp s with
    | none => none
    | some (.push _, r) => opSuccessScan fuel r
    | some (.op c, r) => if isOpSuccess c.toNat then some true else opSuccessScan fuel r

/-- The context of a Tapscript execution. -/
structure TapCtx where
  flags : BitcoinScript.Flags
  tx : Tx
  spent : List TxOut
  nIn : Nat

/-- The hash oracle for the non-signature opcodes (signature opcodes are handled by the Tapscript
loop itself; the oracle's `checkSig` is never consulted). -/
def tapOracle (c : TapCtx) : Oracle where
  ripemd160 := BitcoinSer.ripemd160
  sha1 := BitcoinSer.sha1
  sha256 := BitcoinSer.sha256
  hash160 := BitcoinSer.hash160
  hash256 := BitcoinSer.hash256
  checkSig := fun _ _ => none
  checkLockTime := BitcoinSig.checkLockTime c.tx c.nIn
  checkSequence := BitcoinSig.checkSequence c.tx c.nIn

/-- The Tapscript execution state: the interpreter state, the validation weight left, the
code-separator position, and the opcode position. -/
structure TapState where
  st : State
  weightLeft : Int
  codeseparatorPos : Nat
  opcodePos : Nat

/-- `EvalChecksigTapscript`: `none` is a script error; otherwise the `success` flag and the new
weight. -/
def evalChecksigTapscript (c : TapCtx) (ed : ExecData) (sig pubkey : Bytes) (weightLeft : Int) : Option (Bool × Int) :=
  let success := !sig.isEmpty
  let weight := if success then weightLeft - VALIDATION_WEIGHT_PER_SIGOP_PASSED else weightLeft
  if success ∧ weight < 0 then none
  else if pubkey.length = 0 then none
  else if pubkey.length = 32 then
    if success ∧ !checkSchnorrSignature c.tx c.spent c.nIn sig pubkey true ed then none
    else some (success, weight)
  else some (success, weight)   -- unknown public key type: `DISCOURAGE_UPGRADABLE_PUBKEYTYPE` is policy

/-- One opcode of `EvalScript` under `SigVersion::TAPSCRIPT`, when executing or a conditional. -/
def tapExecOp (c : TapCtx) (ed : ExecData) (fExec : Bool) (op : Byte) (ts : TapState) : Option TapState :=
  let s := ts.st
  let ed' := { ed with codeseparatorPos := ts.codeseparatorPos }
  if op == BitcoinScript.OP_IF || op == BitcoinScript.OP_NOTIF then
    -- `MINIMALIF` is consensus in Tapscript
    if fExec then
      match s.stack with
      | [] => none
      | top :: _ =>
        if 1 < top.length ∨ (top.length = 1 ∧ (top.getD 0 0).toNat ≠ 1) then none
        else (BitcoinScript.execOp c.flags (tapOracle c) fExec op s).map fun s' => { ts with st := s' }
    else (BitcoinScript.execOp c.flags (tapOracle c) fExec op s).map fun s' => { ts with st := s' }
  else if op == BitcoinScript.OP_CHECKSIG || op == BitcoinScript.OP_CHECKSIGVERIFY then
    match s.stack with
    | pubkey :: sig :: rest =>
      match evalChecksigTapscript c ed' sig pubkey ts.weightLeft with
      | none => none
      | some (success, weight) =>
        if op == BitcoinScript.OP_CHECKSIGVERIFY then
          if success then some { ts with st := { s with stack := rest }, weightLeft := weight } else none
        else some { ts with st := { s with stack := BitcoinScript.boolBytes success :: rest }, weightLeft := weight }
    | _ => none
  else if op == OP_CHECKSIGADD then
    -- (sig num pubkey -- num)
    match s.stack with
    | pubkey :: numv :: sig :: rest =>
      match BitcoinScript.toNum false 4 numv with
      | none => none
      | some num =>
        match evalChecksigTapscript c ed' sig pubkey ts.weightLeft with
        | none => none
        | some (success, weight) =>
          some { ts with st := { s with stack := BitcoinScript.serialize (num + (if success then 1 else 0)) :: rest },
                         weightLeft := weight }
    | _ => none
  else if op == BitcoinScript.OP_CHECKMULTISIG || op == BitcoinScript.OP_CHECKMULTISIGVERIFY then none
  else if op == BitcoinScript.OP_CODESEPARATOR then
    some { ts with codeseparatorPos := ts.opcodePos }
  else (BitcoinScript.execOp c.flags (tapOracle c) fExec op s).map fun s' => { ts with st := s' }

/-- One loop iteration of `EvalScript` under Tapscript: no operation count; the push-size test; the
disabled-opcode test (never reached, every disabled opcode being an `OP_SUCCESSx`); execute or skip;
the stack-size test; the opcode position advances on every instruction. -/
def tapStep (c : TapCtx) (ed : ExecData) (ts : TapState) : Instr → Option TapState
  | .push data =>
    let s := ts.st
    if BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE < data.length then none
    else
      let s' := if BitcoinScript.allTrue s.vfExec then { s with stack := data :: s.stack } else s
      if BitcoinScript.MAX_STACK_SIZE < s'.stack.length + s'.altstack.length then none
      else some { ts with st := s', opcodePos := ts.opcodePos + 1 }
  | .op op =>
    let s := ts.st
    let fExec := BitcoinScript.allTrue s.vfExec
    if BitcoinScript.isDisabled op then none
    else
      let r : Option TapState :=
        if fExec || (BitcoinScript.OP_IF ≤ op && op ≤ BitcoinScript.OP_ENDIF) then tapExecOp c ed fExec op ts
        else some ts
      match r with
      | none => none
      | some ts' =>
        if BitcoinScript.MAX_STACK_SIZE < ts'.st.stack.length + ts'.st.altstack.length then none
        else some { ts' with opcodePos := ts'.opcodePos + 1 }

def tapRun (c : TapCtx) (ed : ExecData) : TapState → Script → Option TapState
  | ts, [] => if ts.st.vfExec.isEmpty then some ts else none
  | ts, i :: rest =>
    match tapStep c ed ts i with
    | none => none
    | some ts' => tapRun c ed ts' rest

/-- `ExecuteWitnessScript(stack, script, flags, SigVersion::TAPSCRIPT, checker, execdata)`: the
`OP_SUCCESSx` scan, the initial stack-size and element-size limits, the run, and the clean-stack
requirement of exactly one true element. `stack` is top-first; `weight` is the initial validation
weight. -/
def executeTapscript (c : TapCtx) (ed : ExecData) (stack : List Bytes) (script : Bytes) (weight : Int) : Bool :=
  match opSuccessScan script.length script with
  | none => false
  | some true => true
  | some false =>
    if BitcoinScript.MAX_STACK_SIZE < stack.length then false
    else if stack.any (fun e => BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE < e.length) then false
    else match BitcoinSig.parseScript script with
      | none => false
      | some s =>
        match tapRun c ed ⟨⟨stack, [], [], 0⟩, weight, 0xFFFFFFFF, 0⟩ s with
        | none => false
        | some ts => decide (ts.st.stack.length = 1) && BitcoinVerify.topTrue ts.st.stack

/-! ### The version-1 branch of `VerifyWitnessProgram` -/

/-- `GetSerializeSize(witness.stack)`. -/
def witnessSerializedSize (witness : List Bytes) : Nat := (BitcoinSer.serList BitcoinSer.serBytes witness).length

/-- The annex: present when at least two elements remain and the last is non-empty and starts
with `0x50`. -/
def hasAnnex (witness : List Bytes) : Bool :=
  decide (2 ≤ witness.length) && (match witness.getLast? with
    | some (b :: _) => decide (b.toNat = ANNEX_TAG)
    | _ => false)

/-- The Taproot branch (version 1, 32-byte program, not P2SH, `TAPROOT` flag set), as a
`BitcoinVerify.TaprootHandler`, for the given spent outputs. -/
def taprootHandler (spent : List TxOut) : BitcoinVerify.TaprootHandler := fun c witness program =>
  if witness.isEmpty then false
  else
    let tc : TapCtx := ⟨BitcoinVerify.scriptFlagsOf c.flags, c.tx, spent, c.nIn⟩
    let annex? : Option Bytes := if hasAnnex witness then witness.getLast? else none
    let stack := if hasAnnex witness then witness.dropLast else witness
    let ed0 : ExecData := ⟨annex?.isSome, (match annex? with
        | some a => BitcoinSer.sha256 (BitcoinSer.serBytes a)
        | none => []), [], 0xFFFFFFFF⟩
    if stack.length = 1 then
      -- key path
      checkSchnorrSignature c.tx spent c.nIn (stack.getD 0 []) program false ed0
    else
      -- script path
      match stack.getLast? with
      | none => false
      | some control =>
        let stack := stack.dropLast
        match stack.getLast? with
        | none => false
        | some script =>
          let stack := stack.dropLast
          if control.length < TAPROOT_CONTROL_BASE_SIZE ∨ TAPROOT_CONTROL_MAX_SIZE < control.length ∨
             (control.length - TAPROOT_CONTROL_BASE_SIZE) % TAPROOT_CONTROL_NODE_SIZE ≠ 0 then false
          else
            let leafVersion := (control.getD 0 0).toNat &&& TAPROOT_LEAF_MASK
            let leafHash := tapleafHash (BitVec.ofNat 8 leafVersion) script
            if !verifyTaprootCommitment control program leafHash then false
            else if leafVersion = TAPROOT_LEAF_TAPSCRIPT then
              executeTapscript tc { ed0 with tapleafHash := leafHash } stack.reverse script
                ((witnessSerializedSize witness : Int) + VALIDATION_WEIGHT_OFFSET)
            else true   -- unknown leaf version: `DISCOURAGE_UPGRADABLE_TAPROOT_VERSION` is policy

/-- The complete `VerifyScript`, with the Taproot branch supplied. -/
def verifyScriptFull (spent : List TxOut) (c : BitcoinVerify.Ctx) (scriptSig scriptPubKey : Bytes)
    (witness : List Bytes) : Bool :=
  BitcoinVerify.verifyScript (taprootHandler spent) c scriptSig scriptPubKey witness

/-- The output script `OP_1 <32-byte key>` of a Taproot output. -/
def p2trBytes (q : Bytes) : Bytes := BitcoinVerify.witnessBytes 1 q

end BitcoinTaproot


