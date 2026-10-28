-- Prove2me | Definitions.Def_BitcoinScript
-- name    : BitcoinScript
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-26T05:42:40.294004+00:00
-- url     : https://prove2.me/theorems/a2e97aac-180a-4949-9121-c1edc4ed5997
-- title:
--   CScriptNum, CastToBool, and the legacy Script interpreter (EvalScript, VerifyScript)
-- statement:
--   A byte is an 8-bit word; a stack element is a list of bytes. Limits: element size $520$, $201$ operations, $20$ keys per multisig, $1000$ stack elements, $4$-byte numbers.
--
--   **Numbers.** $\mathrm{leNat}$ is the little-endian value of a byte list; $\mathrm{topBit}$ is bit 7 of the last byte; $\mathrm{clearTop}$ clears it; $\mathrm{setVch}(v)$ is `CScriptNum::set_vch`: $-\mathrm{leNat}(\mathrm{clearTop}\,v)$ when the top bit is set, else $\mathrm{leNat}(v)$, and $0$ for the empty list. $\mathrm{natBytes}(n)$ is the little-endian byte loop without trailing zeros; $\mathrm{setTop}$ sets bit 7 of the last byte; $\mathrm{serialize}(n)$ is `CScriptNum::serialize`: empty for $0$, else the magnitude bytes with a sign byte `0x80`/`0x00` appended when their top bit is already set, or the top bit set for a negative value otherwise. $\mathrm{nonMinimal}(v)$ is the constructor's rejection test (last byte has no value bits and the previous byte does not need it); $\mathrm{toNum}(\text{requireMinimal}, \text{maxSize}, v)$ is the constructor, `none` where it throws. $\mathrm{castToBool}$ is `CastToBool`; `vchTrue` $= [1]$, `vchFalse` $= [\,]$.
--
--   **Scripts.** An instruction is a data push or a non-push opcode byte; a script is a list of instructions, the output of `GetOp`. Opcode constants follow `script.h`; `isDisabled` lists the fifteen CVE-2010-5137 opcodes.
--
--   **Flags and oracle.** `Flags` holds `CHECKLOCKTIMEVERIFY`, `CHECKSEQUENCEVERIFY`, `NULLDUMMY`. An `Oracle` supplies `ripemd160`, `sha1`, `sha256`, `hash160`, `hash256`, `checkSig` (returning `none` where an encoding check fails the script, `some b` for the signature verdict), `checkLockTime` and `checkSequence`.
--
--   **Execution.** A `State` is the main stack, alt stack, condition stack and `nOpCount`, stacks top-first. `execOp`(flags, oracle, fExec, opcode, state) is the `switch` of `EvalScript` for one opcode: small-integer pushes, `NOP`s, `CHECKLOCKTIMEVERIFY`/`CHECKSEQUENCEVERIFY` (5-byte numbers, negative rejected, disable flag), `IF`/`NOTIF`/`ELSE`/`ENDIF`, `VERIFY`, `RETURN`, the stack family (`TOALTSTACK` … `TUCK`, `SIZE`), `EQUAL`/`EQUALVERIFY`, the unary and binary numeric family on 4-byte operands, `WITHIN`, the five hash opcodes, `CODESEPARATOR`, `CHECKSIG`/`CHECKSIGVERIFY`, `CHECKMULTISIG`/`CHECKMULTISIGVERIFY` with key-count accounting, the `NULLDUMMY` test and the extra popped element; anything else is a bad opcode. `step` is one loop iteration: element-size check and conditional push for a push; for an opcode, the `nOpCount` increment and $201$ test (only for opcodes above `OP_16`: `OP_1NEGATE`, `OP_RESERVED` and `OP_1`…`OP_16` are not counted, as in the source), the disabled test, execute-or-skip, and the stack-size check. `run` is the loop plus the final unbalanced-conditional check; `evalScript` returns the main stack; `verifyScriptPlain` is `VerifyScript` for a `scriptPubKey` that is neither P2SH nor a witness program. `p2pkhScript` and `p2pkScript` are the two templates; `opsIn` counts the instructions `nOpCount` counts: non-push opcodes above `OP_16`.
--
--   **Formalization Note.** `SigVersion::BASE` only; `fRequireMinimal` false; policy flags off; byte-level parsing, `MAX_SCRIPT_SIZE`, P2SH, witness programs and Tapscript are out of scope. An `op` instruction is meant for the bytes `GetOp` returns as non-push opcodes (above `OP_PUSHDATA4`); a push-range byte used as `op` behaves like an unknown opcode. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CastToBool (lines 46-59), EvalScript (417-1249), EvalChecksigPreTapscript, VerifyScript (2012-2110), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScriptNum (227-382), opcodetype, MAX_SCRIPT_ELEMENT_SIZE, MAX_OPS_PER_SCRIPT, MAX_PUBKEYS_PER_MULTISIG, MAX_STACK_SIZE, src/script/script.h; GetScriptOp, IsPushOnly, IsPayToScriptHash, src/script/script.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h

import Std

namespace BitcoinScript

/-! Transcription of the Bitcoin Script interpreter of Bitcoin Core at revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48` for the legacy (`SigVersion::BASE`) execution path:
`CScriptNum` (`script/script.h`), `CastToBool`, `EvalScript` and `VerifyScript`
(`script/interpreter.cpp`), with the consensus limits of `script/script.h`.

Conventions. A byte is an 8-bit word; a stack element (`valtype`) is a list of bytes. A script is
the sequence of instructions that `GetOp` yields when parsing it: a data push (opcodes `OP_0` to
`OP_PUSHDATA4`, carrying the pushed bytes) or a non-push opcode, so byte-level parsing and the
`MAX_SCRIPT_SIZE` bound on the serialized script belong to the serialization layer. Stacks are
lists with the top element first, so `stacktop(-1)` is the head. Hash functions, the lock-time
and sequence checks, and the signature check (including signature and public-key encoding checks
and `FindAndDelete`) are supplied by an abstract `Oracle`, as they are by `BaseSignatureChecker`
and the hash primitives in the source. -/

abbrev Byte := BitVec 8
abbrev Bytes := List Byte

/-- `script/script.h`: `MAX_SCRIPT_ELEMENT_SIZE = 520`. -/
def MAX_SCRIPT_ELEMENT_SIZE : Nat := 520
/-- `script/script.h`: `MAX_OPS_PER_SCRIPT = 201`. -/
def MAX_OPS_PER_SCRIPT : Nat := 201
/-- `script/script.h`: `MAX_PUBKEYS_PER_MULTISIG = 20`. -/
def MAX_PUBKEYS_PER_MULTISIG : Nat := 20
/-- `script/script.h`: `MAX_STACK_SIZE = 1000`. -/
def MAX_STACK_SIZE : Nat := 1000
/-- `CScriptNum::nDefaultMaxNumSize = 4`. -/
def nDefaultMaxNumSize : Nat := 4

/-! ### CScriptNum -/

/-- Little-endian value of a byte list. -/
def leNat : Bytes → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * leNat rest

/-- The sign bit `0x80` of the last byte, if any. -/
def topBit : Bytes → Bool
  | [] => false
  | [b] => (b &&& 0x80) != 0
  | _ :: rest => topBit rest

/-- Clear the sign bit of the last byte: `result & ~(0x80ULL << (8 * (vch.size() - 1)))`. -/
def clearTop : Bytes → Bytes
  | [] => []
  | [b] => [b &&& 0x7f]
  | b :: rest => b :: clearTop rest

/-- `CScriptNum::set_vch`: little-endian magnitude with the top bit as the sign; `0` for empty. -/
def setVch (v : Bytes) : Int :=
  if topBit v then -((leNat (clearTop v) : Nat) : Int) else ((leNat v : Nat) : Int)

/-- Little-endian bytes of a natural number, no trailing zero bytes: the `while (absvalue)` loop. -/
def natBytes (n : Nat) : Bytes :=
  if h : n = 0 then [] else BitVec.ofNat 8 (n % 256) :: natBytes (n / 256)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- Set the sign bit of the last byte: `result.back() |= 0x80`. -/
def setTop : Bytes → Bytes
  | [] => []
  | [b] => [b ||| 0x80]
  | b :: rest => b :: setTop rest

/-- `CScriptNum::serialize`. -/
def serialize (v : Int) : Bytes :=
  if v = 0 then []
  else
    let neg := v < 0
    let mag := natBytes v.natAbs
    if topBit mag then mag ++ [if neg then 0x80 else 0]
    else if neg then setTop mag else mag

/-- The minimal-encoding test of the `CScriptNum(vch, fRequireMinimal)` constructor: the last byte
has no value bits, and the previous byte does not need the sign byte. `true` means non-minimal. -/
def nonMinimal (v : Bytes) : Bool :=
  match v.reverse with
  | [] => false
  | last :: before =>
    (last &&& 0x7f) == 0 &&
      (match before with
       | [] => true
       | prev :: _ => (prev &&& 0x80) == 0)

/-- `CScriptNum(vch, fRequireMinimal, nMaxNumSize)`: `none` where the constructor throws. -/
def toNum (requireMinimal : Bool) (maxSize : Nat) (v : Bytes) : Option Int :=
  if maxSize < v.length then none
  else if requireMinimal && !v.isEmpty && nonMinimal v then none
  else some (setVch v)

/-- `CastToBool`: some byte is nonzero, except that a negative zero (`0x80` as the last byte after
zero bytes) is false. -/
def castToBool : Bytes → Bool
  | [] => false
  | [b] => b != 0 && b != 0x80
  | b :: rest => b != 0 || castToBool rest

/-- `vchTrue` and `vchFalse`. -/
def vchTrue : Bytes := [1]
def vchFalse : Bytes := []
def boolBytes (b : Bool) : Bytes := if b then vchTrue else vchFalse

/-! ### Scripts -/

/-- One parsed instruction: a data push (any of `OP_0`, direct pushes, `OP_PUSHDATAn`), or a
non-push opcode given by its byte. `GetOp` only ever yields `op c` with `OP_PUSHDATA4 < c`; a
byte in the push range used as `op` behaves like an unknown opcode. -/
inductive Instr where
  | push (data : Bytes)
  | op (code : Byte)
  deriving DecidableEq, Repr

abbrev Script := List Instr

/-- Opcode bytes used below (`script/script.h`). -/
def OP_1NEGATE : Byte := 0x4f
def OP_RESERVED : Byte := 0x50
def OP_1 : Byte := 0x51
def OP_16 : Byte := 0x60
def OP_NOP : Byte := 0x61
def OP_IF : Byte := 0x63
def OP_NOTIF : Byte := 0x64
def OP_ELSE : Byte := 0x67
def OP_ENDIF : Byte := 0x68
def OP_VERIFY : Byte := 0x69
def OP_RETURN : Byte := 0x6a
def OP_TOALTSTACK : Byte := 0x6b
def OP_FROMALTSTACK : Byte := 0x6c
def OP_2DROP : Byte := 0x6d
def OP_2DUP : Byte := 0x6e
def OP_3DUP : Byte := 0x6f
def OP_2OVER : Byte := 0x70
def OP_2ROT : Byte := 0x71
def OP_2SWAP : Byte := 0x72
def OP_IFDUP : Byte := 0x73
def OP_DEPTH : Byte := 0x74
def OP_DROP : Byte := 0x75
def OP_DUP : Byte := 0x76
def OP_NIP : Byte := 0x77
def OP_OVER : Byte := 0x78
def OP_PICK : Byte := 0x79
def OP_ROLL : Byte := 0x7a
def OP_ROT : Byte := 0x7b
def OP_SWAP : Byte := 0x7c
def OP_TUCK : Byte := 0x7d
def OP_CAT : Byte := 0x7e
def OP_SUBSTR : Byte := 0x7f
def OP_LEFT : Byte := 0x80
def OP_RIGHT : Byte := 0x81
def OP_SIZE : Byte := 0x82
def OP_INVERT : Byte := 0x83
def OP_AND : Byte := 0x84
def OP_OR : Byte := 0x85
def OP_XOR : Byte := 0x86
def OP_EQUAL : Byte := 0x87
def OP_EQUALVERIFY : Byte := 0x88
def OP_1ADD : Byte := 0x8b
def OP_1SUB : Byte := 0x8c
def OP_2MUL : Byte := 0x8d
def OP_2DIV : Byte := 0x8e
def OP_NEGATE : Byte := 0x8f
def OP_ABS : Byte := 0x90
def OP_NOT : Byte := 0x91
def OP_0NOTEQUAL : Byte := 0x92
def OP_ADD : Byte := 0x93
def OP_SUB : Byte := 0x94
def OP_MUL : Byte := 0x95
def OP_DIV : Byte := 0x96
def OP_MOD : Byte := 0x97
def OP_LSHIFT : Byte := 0x98
def OP_RSHIFT : Byte := 0x99
def OP_BOOLAND : Byte := 0x9a
def OP_BOOLOR : Byte := 0x9b
def OP_NUMEQUAL : Byte := 0x9c
def OP_NUMEQUALVERIFY : Byte := 0x9d
def OP_NUMNOTEQUAL : Byte := 0x9e
def OP_LESSTHAN : Byte := 0x9f
def OP_GREATERTHAN : Byte := 0xa0
def OP_LESSTHANOREQUAL : Byte := 0xa1
def OP_GREATERTHANOREQUAL : Byte := 0xa2
def OP_MIN : Byte := 0xa3
def OP_MAX : Byte := 0xa4
def OP_WITHIN : Byte := 0xa5
def OP_RIPEMD160 : Byte := 0xa6
def OP_SHA1 : Byte := 0xa7
def OP_SHA256 : Byte := 0xa8
def OP_HASH160 : Byte := 0xa9
def OP_HASH256 : Byte := 0xaa
def OP_CODESEPARATOR : Byte := 0xab
def OP_CHECKSIG : Byte := 0xac
def OP_CHECKSIGVERIFY : Byte := 0xad
def OP_CHECKMULTISIG : Byte := 0xae
def OP_CHECKMULTISIGVERIFY : Byte := 0xaf
def OP_NOP1 : Byte := 0xb0
def OP_CHECKLOCKTIMEVERIFY : Byte := 0xb1
def OP_CHECKSEQUENCEVERIFY : Byte := 0xb2
def OP_NOP4 : Byte := 0xb3
def OP_NOP10 : Byte := 0xb9

/-- The fifteen opcodes disabled since CVE-2010-5137; rejected even in an unexecuted branch. -/
def isDisabled (c : Byte) : Bool :=
  c == OP_CAT || c == OP_SUBSTR || c == OP_LEFT || c == OP_RIGHT || c == OP_INVERT ||
  c == OP_AND || c == OP_OR || c == OP_XOR || c == OP_2MUL || c == OP_2DIV || c == OP_MUL ||
  c == OP_DIV || c == OP_MOD || c == OP_LSHIFT || c == OP_RSHIFT

/-! ### Flags and the oracle -/

/-- The consensus script-verification flags that affect legacy execution. `MINIMALDATA`,
`NULLFAIL`, `CONST_SCRIPTCODE`, `DISCOURAGE_UPGRADABLE_NOPS` and `MINIMALIF` are policy flags and
are modeled as off. -/
structure Flags where
  cltv : Bool
  csv : Bool
  nulldummy : Bool

/-- The primitives the interpreter calls out to. `checkSig sig pubkey` is `EvalChecksig` for
`SigVersion::BASE`: `none` when a signature or public-key encoding check fails the script,
otherwise `some` of `CheckECDSASignature` with the `scriptCode` the checker holds. -/
structure Oracle where
  ripemd160 : Bytes → Bytes
  sha1 : Bytes → Bytes
  sha256 : Bytes → Bytes
  hash160 : Bytes → Bytes
  hash256 : Bytes → Bytes
  checkSig : Bytes → Bytes → Option Bool
  checkLockTime : Int → Bool
  checkSequence : Int → Bool

/-- `CTxIn::SEQUENCE_LOCKTIME_DISABLE_FLAG = (1U << 31)`. -/
def SEQUENCE_LOCKTIME_DISABLE_FLAG : Nat := 2147483648

/-! ### Execution state -/

/-- The interpreter's mutable state: main stack, alt stack, the condition stack `vfExec`, and
`nOpCount`. Stacks hold the top element first. -/
structure State where
  stack : List Bytes
  altstack : List Bytes
  vfExec : List Bool
  opCount : Nat

def State.initial (stack : List Bytes) : State := ⟨stack, [], [], 0⟩

/-- `vfExec.all_true()`. -/
def allTrue (l : List Bool) : Bool := l.all id

/-- The numeric result of an opcode, pushed as `bn.getvch()`. -/
def pushNum (s : State) (n : Int) : State := { s with stack := serialize n :: s.stack }

/-- Remove the element at index `i` (0 = top). -/
def eraseAt : List Bytes → Nat → List Bytes
  | [], _ => []
  | _ :: r, 0 => r
  | x :: r, n + 1 => x :: eraseAt r n

/-- The `CHECKMULTISIG` matching loop: signatures and keys top-first, the keys consumed in
order, each signature matched against successive keys; fails when more signatures remain than
keys. `none` when an encoding check fails the script. -/
def multisigLoop (o : Oracle) : List Bytes → List Bytes → Option Bool
  | [], _ => some true
  | _ :: _, [] => some false
  | sig :: sigs, key :: keys =>
    match o.checkSig sig key with
    | none => none
    | some ok =>
      if ok then
        if keys.length < sigs.length then some false else multisigLoop o sigs keys
      else
        if keys.length < (sig :: sigs).length then some false else multisigLoop o (sig :: sigs) keys

/-- Execute one non-push opcode that is being executed (or is a conditional), as the `switch` of
`EvalScript`. `none` is script failure. -/
def execOp (f : Flags) (o : Oracle) (fExec : Bool) (c : Byte) (s : State) : Option State :=
  -- OP_1NEGATE, OP_1 … OP_16
  if c == OP_1NEGATE || (OP_1 ≤ c && c ≤ OP_16) then
    some (pushNum s ((c.toNat : Int) - ((OP_1.toNat : Int) - 1)))
  else if c == OP_NOP then some s
  else if c == OP_CHECKLOCKTIMEVERIFY then
    if !f.cltv then some s
    else match s.stack with
      | [] => none
      | top :: _ =>
        match toNum false 5 top with
        | none => none
        | some n => if n < 0 then none else if !o.checkLockTime n then none else some s
  else if c == OP_CHECKSEQUENCEVERIFY then
    if !f.csv then some s
    else match s.stack with
      | [] => none
      | top :: _ =>
        match toNum false 5 top with
        | none => none
        | some n =>
          if n < 0 then none
          else if (n.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) != 0 then some s
          else if !o.checkSequence n then none else some s
  else if c == OP_NOP1 || (OP_NOP4 ≤ c && c ≤ OP_NOP10) then some s
  else if c == OP_IF || c == OP_NOTIF then
    if fExec then
      match s.stack with
      | [] => none
      | top :: rest =>
        let v := castToBool top
        let v := if c == OP_NOTIF then !v else v
        some { s with stack := rest, vfExec := v :: s.vfExec }
    else some { s with vfExec := false :: s.vfExec }
  else if c == OP_ELSE then
    match s.vfExec with
    | [] => none
    | b :: rest => some { s with vfExec := (!b) :: rest }
  else if c == OP_ENDIF then
    match s.vfExec with
    | [] => none
    | _ :: rest => some { s with vfExec := rest }
  else if c == OP_VERIFY then
    match s.stack with
    | [] => none
    | top :: rest => if castToBool top then some { s with stack := rest } else none
  else if c == OP_RETURN then none
  -- stack ops
  else if c == OP_TOALTSTACK then
    match s.stack with
    | [] => none
    | top :: rest => some { s with stack := rest, altstack := top :: s.altstack }
  else if c == OP_FROMALTSTACK then
    match s.altstack with
    | [] => none
    | top :: rest => some { s with stack := top :: s.stack, altstack := rest }
  else if c == OP_2DROP then
    match s.stack with
    | _ :: _ :: rest => some { s with stack := rest }
    | _ => none
  else if c == OP_2DUP then
    match s.stack with
    | a :: b :: rest => some { s with stack := a :: b :: a :: b :: rest }
    | _ => none
  else if c == OP_3DUP then
    match s.stack with
    | a :: b :: d :: rest => some { s with stack := a :: b :: d :: a :: b :: d :: rest }
    | _ => none
  else if c == OP_2OVER then
    match s.stack with
    | x4 :: x3 :: x2 :: x1 :: rest => some { s with stack := x2 :: x1 :: x4 :: x3 :: x2 :: x1 :: rest }
    | _ => none
  else if c == OP_2ROT then
    match s.stack with
    | x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: rest => some { s with stack := x2 :: x1 :: x6 :: x5 :: x4 :: x3 :: rest }
    | _ => none
  else if c == OP_2SWAP then
    match s.stack with
    | x4 :: x3 :: x2 :: x1 :: rest => some { s with stack := x2 :: x1 :: x4 :: x3 :: rest }
    | _ => none
  else if c == OP_IFDUP then
    match s.stack with
    | [] => none
    | top :: rest => some { s with stack := if castToBool top then top :: top :: rest else top :: rest }
  else if c == OP_DEPTH then some (pushNum s s.stack.length)
  else if c == OP_DROP then
    match s.stack with
    | [] => none
    | _ :: rest => some { s with stack := rest }
  else if c == OP_DUP then
    match s.stack with
    | [] => none
    | top :: rest => some { s with stack := top :: top :: rest }
  else if c == OP_NIP then
    match s.stack with
    | a :: _ :: rest => some { s with stack := a :: rest }
    | _ => none
  else if c == OP_OVER then
    match s.stack with
    | a :: b :: rest => some { s with stack := b :: a :: b :: rest }
    | _ => none
  else if c == OP_PICK || c == OP_ROLL then
    match s.stack with
    | top :: rest =>
      if rest.isEmpty then none
      else match toNum false nDefaultMaxNumSize top with
        | none => none
        | some n =>
          if n < 0 || (rest.length : Int) ≤ n then none
          else
            let i := n.toNat
            match rest[i]? with
            | none => none
            | some v =>
              if c == OP_ROLL then some { s with stack := v :: eraseAt rest i }
              else some { s with stack := v :: rest }
    | [] => none
  else if c == OP_ROT then
    match s.stack with
    | x3 :: x2 :: x1 :: rest => some { s with stack := x1 :: x3 :: x2 :: rest }
    | _ => none
  else if c == OP_SWAP then
    match s.stack with
    | a :: b :: rest => some { s with stack := b :: a :: rest }
    | _ => none
  else if c == OP_TUCK then
    match s.stack with
    | x2 :: x1 :: rest => some { s with stack := x2 :: x1 :: x2 :: rest }
    | _ => none
  else if c == OP_SIZE then
    match s.stack with
    | [] => none
    | top :: _ => some (pushNum s top.length)
  -- bitwise logic
  else if c == OP_EQUAL || c == OP_EQUALVERIFY then
    match s.stack with
    | a :: b :: rest =>
      let eq := decide (b = a)
      if c == OP_EQUALVERIFY then (if eq then some { s with stack := rest } else none)
      else some { s with stack := boolBytes eq :: rest }
    | _ => none
  -- numeric
  else if c == OP_1ADD || c == OP_1SUB || c == OP_NEGATE || c == OP_ABS || c == OP_NOT || c == OP_0NOTEQUAL then
    match s.stack with
    | [] => none
    | top :: rest =>
      match toNum false nDefaultMaxNumSize top with
      | none => none
      | some n =>
        let r : Int :=
          if c == OP_1ADD then n + 1 else if c == OP_1SUB then n - 1
          else if c == OP_NEGATE then -n else if c == OP_ABS then (if n < 0 then -n else n)
          else if c == OP_NOT then (if n = 0 then 1 else 0) else (if n ≠ 0 then 1 else 0)
        some (pushNum { s with stack := rest } r)
  else if c == OP_ADD || c == OP_SUB || c == OP_BOOLAND || c == OP_BOOLOR || c == OP_NUMEQUAL ||
      c == OP_NUMEQUALVERIFY || c == OP_NUMNOTEQUAL || c == OP_LESSTHAN || c == OP_GREATERTHAN ||
      c == OP_LESSTHANOREQUAL || c == OP_GREATERTHANOREQUAL || c == OP_MIN || c == OP_MAX then
    match s.stack with
    | a :: b :: rest =>
      match toNum false nDefaultMaxNumSize b, toNum false nDefaultMaxNumSize a with
      | some n1, some n2 =>
        let r : Int :=
          if c == OP_ADD then n1 + n2 else if c == OP_SUB then n1 - n2
          else if c == OP_BOOLAND then (if n1 ≠ 0 ∧ n2 ≠ 0 then 1 else 0)
          else if c == OP_BOOLOR then (if n1 ≠ 0 ∨ n2 ≠ 0 then 1 else 0)
          else if c == OP_NUMEQUAL || c == OP_NUMEQUALVERIFY then (if n1 = n2 then 1 else 0)
          else if c == OP_NUMNOTEQUAL then (if n1 ≠ n2 then 1 else 0)
          else if c == OP_LESSTHAN then (if n1 < n2 then 1 else 0)
          else if c == OP_GREATERTHAN then (if n1 > n2 then 1 else 0)
          else if c == OP_LESSTHANOREQUAL then (if n1 ≤ n2 then 1 else 0)
          else if c == OP_GREATERTHANOREQUAL then (if n1 ≥ n2 then 1 else 0)
          else if c == OP_MIN then (if n1 < n2 then n1 else n2)
          else (if n1 > n2 then n1 else n2)
        if c == OP_NUMEQUALVERIFY then (if r ≠ 0 then some { s with stack := rest } else none)
        else some (pushNum { s with stack := rest } r)
      | _, _ => none
    | _ => none
  else if c == OP_WITHIN then
    match s.stack with
    | a :: b :: d :: rest =>
      match toNum false nDefaultMaxNumSize d, toNum false nDefaultMaxNumSize b, toNum false nDefaultMaxNumSize a with
      | some n1, some n2, some n3 => some { s with stack := boolBytes (decide (n2 ≤ n1 ∧ n1 < n3)) :: rest }
      | _, _, _ => none
    | _ => none
  -- crypto
  else if c == OP_RIPEMD160 || c == OP_SHA1 || c == OP_SHA256 || c == OP_HASH160 || c == OP_HASH256 then
    match s.stack with
    | [] => none
    | top :: rest =>
      let h := if c == OP_RIPEMD160 then o.ripemd160 top else if c == OP_SHA1 then o.sha1 top
        else if c == OP_SHA256 then o.sha256 top else if c == OP_HASH160 then o.hash160 top else o.hash256 top
      some { s with stack := h :: rest }
  else if c == OP_CODESEPARATOR then some s
  else if c == OP_CHECKSIG || c == OP_CHECKSIGVERIFY then
    match s.stack with
    | pubkey :: sig :: rest =>
      match o.checkSig sig pubkey with
      | none => none
      | some ok =>
        if c == OP_CHECKSIGVERIFY then (if ok then some { s with stack := rest } else none)
        else some { s with stack := boolBytes ok :: rest }
    | _ => none
  else if c == OP_CHECKMULTISIG || c == OP_CHECKMULTISIGVERIFY then
    match s.stack with
    | [] => none
    | nk :: rest =>
      match toNum false nDefaultMaxNumSize nk with
      | none => none
      | some nKeys =>
        if nKeys < 0 || (MAX_PUBKEYS_PER_MULTISIG : Int) < nKeys then none
        else
          let opCount := s.opCount + nKeys.toNat
          if MAX_OPS_PER_SCRIPT < opCount then none
          else
            let keys := rest.take nKeys.toNat
            let rest := rest.drop nKeys.toNat
            if keys.length ≠ nKeys.toNat then none
            else match rest with
            | [] => none
            | ns :: rest =>
              match toNum false nDefaultMaxNumSize ns with
              | none => none
              | some nSigs =>
                if nSigs < 0 || nKeys < nSigs then none
                else
                  let sigs := rest.take nSigs.toNat
                  let rest := rest.drop nSigs.toNat
                  if sigs.length ≠ nSigs.toNat then none
                  else match multisigLoop o sigs keys with
                  | none => none
                  | some ok =>
                    match rest with
                    | [] => none
                    | dummy :: rest =>
                      if f.nulldummy && !dummy.isEmpty then none
                      else
                        let s' := { s with stack := rest, opCount := opCount }
                        if c == OP_CHECKMULTISIGVERIFY then (if ok then some s' else none)
                        else some { s' with stack := boolBytes ok :: rest }
  else none

/-- One iteration of the `for (; pc < pend; …)` loop of `EvalScript`. -/
def step (f : Flags) (o : Oracle) (s : State) : Instr → Option State
  | .push data =>
    if MAX_SCRIPT_ELEMENT_SIZE < data.length then none
    else
      let s' := if allTrue s.vfExec then { s with stack := data :: s.stack } else s
      if MAX_STACK_SIZE < s'.stack.length + s'.altstack.length then none else some s'
  | .op c =>
    let fExec := allTrue s.vfExec
    -- `if (opcode > OP_16 && ++nOpCount > MAX_OPS_PER_SCRIPT)`: `OP_1NEGATE`, `OP_RESERVED` and
    -- `OP_1` … `OP_16` do not count towards the limit.
    let counted := decide (OP_16 < c)
    if counted && decide (MAX_OPS_PER_SCRIPT < s.opCount + 1) then none
    else
      let s := if counted then { s with opCount := s.opCount + 1 } else s
      if isDisabled c then none
      else if fExec || (OP_IF ≤ c && c ≤ OP_ENDIF) then
        match execOp f o fExec c s with
        | none => none
        | some s' => if MAX_STACK_SIZE < s'.stack.length + s'.altstack.length then none else some s'
      else if MAX_STACK_SIZE < s.stack.length + s.altstack.length then none else some s

/-- The loop over the instructions, followed by the unbalanced-conditional check. -/
def run (f : Flags) (o : Oracle) : State → Script → Option State
  | s, [] => if s.vfExec.isEmpty then some s else none
  | s, i :: rest =>
    match step f o s i with
    | none => none
    | some s' => run f o s' rest

/-- `EvalScript(stack, script, flags, checker, SigVersion::BASE)`: the resulting main stack. -/
def evalScript (f : Flags) (o : Oracle) (stack : List Bytes) (script : Script) : Option (List Bytes) :=
  (run f o (State.initial stack) script).map State.stack

/-- `VerifyScript` for a `scriptPubKey` that is neither pay-to-script-hash nor a witness
program: evaluate `scriptSig`, then `scriptPubKey` on the same stack, and require a true top. -/
def verifyScriptPlain (f : Flags) (o : Oracle) (scriptSig scriptPubKey : Script) : Bool :=
  match evalScript f o [] scriptSig with
  | none => false
  | some stack =>
    match evalScript f o stack scriptPubKey with
    | none => false
    | some [] => false
    | some (top :: _) => castToBool top

/-- The pay-to-public-key-hash output script `DUP HASH160 <h> EQUALVERIFY CHECKSIG`. -/
def p2pkhScript (h : Bytes) : Script :=
  [.op OP_DUP, .op OP_HASH160, .push h, .op OP_EQUALVERIFY, .op OP_CHECKSIG]

/-- The pay-to-public-key output script `<pubkey> CHECKSIG`. -/
def p2pkScript (pubkey : Bytes) : Script := [.push pubkey, .op OP_CHECKSIG]

/-- Number of instructions `nOpCount` counts: non-push opcodes above `OP_16`. -/
def opsIn : Script → Nat
  | [] => 0
  | .push _ :: rest => opsIn rest
  | .op c :: rest => opsIn rest + (if OP_16 < c then 1 else 0)

end BitcoinScript


