-- Prove2me | Definitions.Def_BitcoinMiniscript
-- name    : BitcoinMiniscript
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T23:22:29.276312+00:00
-- url     : https://prove2.me/theorems/7cfab32f-3c5e-4179-ac22-31daaade5393
-- title:
--   Miniscript fragments, their translation to Script, the type system, and a satisfaction semantics
-- statement:
--   A Miniscript core over the script mission's interpreter.
--
--   **`Ms`** — 23 fragments: `pk_k`, `pk_h`, `older`, `after`, `sha256`, `hash256`, `ripemd160`, `hash160`, `and_v`, `and_b`, `or_b`, `or_c`, `or_d`, `or_i`, `andor`, `multi`, and the wrappers `a:`, `s:`, `c:`, `d:`, `v:`, `j:`, `n:`. **`compile`** — the reference's translation table into the script mission's instruction lists (numbers through `CScript << int64`; `v:` appends an explicit `OP_VERIFY`, the reference's folding into a preceding `*VERIFY` opcode is not modelled). **`size`**, **`opsMax`** — the instruction count and an upper bound on counted opcodes.
--
--   **`Ty`** — the basic types `B`, `V`, `K`, `W`; **`Props`**, **`props`** — the modifiers `z`, `o`, `n`, `d`, `u` computed by the reference's table; **`HasType`** — the typing rules (with size bounds on pushed data, `1 ≤ n < 2^31` for time locks, `1 ≤ k ≤ |keys| ≤ 20` for `multi`); **`typeOf`** — a decidable type checker.
--
--   **`Sem f o m w out`** — the witness `w` (top first) drives `m` to the output `out` left above the untouched stack: `[v]` for `B`/`W` (nonzero for a satisfaction, empty for a dissatisfaction), `[]` for `V`, `[key, sig]` for `K`. It follows the reference's satisfaction and dissatisfaction tables and includes the non-canonical combinations the script also accepts. **`Sat`**, **`Dsat`**, **`SatV`** — satisfaction (a true output), dissatisfaction (the empty output), and `V` satisfaction (no output). **`GoodVal v`** — `v` is the script number of some $0 \le n < 2^{31}$. **`runSeq`** — the interpreter's instruction loop without the final unbalanced-conditional check, so that it composes.
--
--   **Formalization Note.** `numInstr`, `CsvPasses` are the `to_local` mission's; `CltvPasses` the HTLC mission's; the interpreter, `Oracle` and `Flags` the script mission's. Only `Std` is imported.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinHtlc

/-!
# A core of Miniscript under Bitcoin's script interpreter

Miniscript (https://bitcoin.sipa.be/miniscript/) is a structured language of spending
conditions, each fragment of which has a fixed translation to Bitcoin Script, a correctness type
(`B`, `V`, `K`, `W`) with type modifiers (`z o n d u`), and a satisfaction table describing the
witness stacks that make the translated script succeed. This file states, for a core subset of
the fragments, the language (`Ms`), the translation (`compile`), the correctness types and the
syntactic type modifiers (`Ty`, `props`, `HasType`), and a satisfaction semantics (`Sem`,
`Sat`, `Dsat`, `SatV`) over the abstract `Oracle` and `Flags` of the script interpreter, so that
the compiler can be proved sound: a witness that satisfies a well-typed fragment makes its
compiled script succeed in the interpreter `BitcoinScript.evalScript`.

Witness stacks are lists with the top element first, as `evalScript` takes them; the Miniscript
tables list witness elements in push order (last pushed on top), so `and_v(X,Y)`'s `satY satX`
is `wX ++ wY` here.
-/

namespace BitcoinMiniscript

open BitcoinScript BitcoinToLocal BitcoinHtlc

/-! ### The language -/

/-- The fragments of the core. The two key fragments `pk_k` and `pk_h` are of type `K` and
become `B` with the `c:` wrapper (`pk(key)` is `c:pk_k(key)`); `pk_h` carries the key hash. -/
inductive Ms where
  | pk_k (key : Bytes)
  | pk_h (keyHash : Bytes)
  | older (n : Int)
  | after (n : Int)
  | sha256 (h : Bytes)
  | hash256 (h : Bytes)
  | ripemd160 (h : Bytes)
  | hash160 (h : Bytes)
  | and_v (x y : Ms)
  | and_b (x y : Ms)
  | or_b (x z : Ms)
  | or_c (x z : Ms)
  | or_d (x z : Ms)
  | or_i (x z : Ms)
  | andor (x y z : Ms)
  | multi (k : Nat) (keys : List Bytes)
  | wrap_a (x : Ms)
  | wrap_s (x : Ms)
  | wrap_c (x : Ms)
  | wrap_d (x : Ms)
  | wrap_v (x : Ms)
  | wrap_j (x : Ms)
  | wrap_n (x : Ms)
  deriving DecidableEq, Repr

/-- The translation table. Numbers are pushed as `CScript << int64` (`BitcoinToLocal.numInstr`);
`v:` appends an explicit `OP_VERIFY` (the folding of `OP_VERIFY` into the preceding `*VERIFY`
opcode is not modeled). -/
def compile : Ms → Script
  | .pk_k key => [.push key]
  | .pk_h h => [.op OP_DUP] ++ [.op OP_HASH160] ++ [.push h] ++ [.op OP_EQUALVERIFY]
  | .older n => [numInstr n] ++ [.op OP_CHECKSEQUENCEVERIFY]
  | .after n => [numInstr n] ++ [.op OP_CHECKLOCKTIMEVERIFY]
  | .sha256 h => [.op OP_SIZE] ++ [numInstr 32] ++ [.op OP_EQUALVERIFY] ++ [.op OP_SHA256] ++ [.push h] ++ [.op OP_EQUAL]
  | .hash256 h => [.op OP_SIZE] ++ [numInstr 32] ++ [.op OP_EQUALVERIFY] ++ [.op OP_HASH256] ++ [.push h] ++ [.op OP_EQUAL]
  | .ripemd160 h => [.op OP_SIZE] ++ [numInstr 32] ++ [.op OP_EQUALVERIFY] ++ [.op OP_RIPEMD160] ++ [.push h] ++ [.op OP_EQUAL]
  | .hash160 h => [.op OP_SIZE] ++ [numInstr 32] ++ [.op OP_EQUALVERIFY] ++ [.op OP_HASH160] ++ [.push h] ++ [.op OP_EQUAL]
  | .and_v x y => compile x ++ compile y
  | .and_b x y => compile x ++ compile y ++ [.op OP_BOOLAND]
  | .or_b x z => compile x ++ compile z ++ [.op OP_BOOLOR]
  | .or_c x z => compile x ++ [.op OP_NOTIF] ++ compile z ++ [.op OP_ENDIF]
  | .or_d x z => compile x ++ [.op OP_IFDUP] ++ [.op OP_NOTIF] ++ compile z ++ [.op OP_ENDIF]
  | .or_i x z => [.op OP_IF] ++ compile x ++ [.op OP_ELSE] ++ compile z ++ [.op OP_ENDIF]
  | .andor x y z => compile x ++ [.op OP_NOTIF] ++ compile z ++ [.op OP_ELSE] ++ compile y ++ [.op OP_ENDIF]
  | .multi k keys => [numInstr k] ++ keys.map Instr.push ++ [numInstr keys.length] ++ [.op OP_CHECKMULTISIG]
  | .wrap_a x => [.op OP_TOALTSTACK] ++ compile x ++ [.op OP_FROMALTSTACK]
  | .wrap_s x => [.op OP_SWAP] ++ compile x
  | .wrap_c x => compile x ++ [.op OP_CHECKSIG]
  | .wrap_d x => [.op OP_DUP] ++ [.op OP_IF] ++ compile x ++ [.op OP_ENDIF]
  | .wrap_v x => compile x ++ [.op OP_VERIFY]
  | .wrap_j x => [.op OP_SIZE] ++ [.op OP_0NOTEQUAL] ++ [.op OP_IF] ++ compile x ++ [.op OP_ENDIF]
  | .wrap_n x => compile x ++ [.op OP_0NOTEQUAL]

/-- The number of instructions of the translation; also a bound on the stack growth while it
runs, since every instruction used pushes at most one element. -/
def size : Ms → Nat
  | .pk_k _ => 1
  | .pk_h _ => 4
  | .older _ => 2
  | .after _ => 2
  | .sha256 _ => 6
  | .hash256 _ => 6
  | .ripemd160 _ => 6
  | .hash160 _ => 6
  | .and_v x y => size x + size y
  | .and_b x y => size x + size y + 1
  | .or_b x z => size x + size z + 1
  | .or_c x z => size x + size z + 2
  | .or_d x z => size x + size z + 3
  | .or_i x z => size x + size z + 3
  | .andor x y z => size x + size y + size z + 3
  | .multi _ keys => keys.length + 3
  | .wrap_a x => size x + 2
  | .wrap_s x => size x + 1
  | .wrap_c x => size x + 1
  | .wrap_d x => size x + 3
  | .wrap_v x => size x + 1
  | .wrap_j x => size x + 4
  | .wrap_n x => size x + 1

/-- An upper bound on what the translation adds to `nOpCount`: its non-push opcodes above
`OP_16`, plus the number of keys for `OP_CHECKMULTISIG` (counted only when executed). -/
def opsMax : Ms → Nat
  | .pk_k _ => 0
  | .pk_h _ => 3
  | .older _ => 1
  | .after _ => 1
  | .sha256 _ => 4
  | .hash256 _ => 4
  | .ripemd160 _ => 4
  | .hash160 _ => 4
  | .and_v x y => opsMax x + opsMax y
  | .and_b x y => opsMax x + opsMax y + 1
  | .or_b x z => opsMax x + opsMax z + 1
  | .or_c x z => opsMax x + opsMax z + 2
  | .or_d x z => opsMax x + opsMax z + 3
  | .or_i x z => opsMax x + opsMax z + 3
  | .andor x y z => opsMax x + opsMax y + opsMax z + 3
  | .multi _ keys => keys.length + 1
  | .wrap_a x => opsMax x + 2
  | .wrap_s x => opsMax x + 1
  | .wrap_c x => opsMax x + 1
  | .wrap_d x => opsMax x + 3
  | .wrap_v x => opsMax x + 1
  | .wrap_j x => opsMax x + 4
  | .wrap_n x => opsMax x + 1

/-! ### Types -/

/-- The correctness types: `B` (base: leaves a nonzero value or exactly `[]`), `V` (verify: leaves
nothing), `K` (key: leaves a public key above its signature), `W` (wrapped: a `B` that takes its
input from below the top element). -/
inductive Ty where
  | B | V | K | W
  deriving DecidableEq, Repr

/-- The type modifiers of the reference's correctness table: `z` (consumes no stack element),
`o` (consumes exactly one), `n` (the top consumed element is nonempty when satisfied), `d`
(has a dissatisfaction), `u` (satisfaction leaves exactly `1`). -/
structure Props where
  z : Bool
  o : Bool
  n : Bool
  d : Bool
  u : Bool
  deriving DecidableEq, Repr

/-- The modifiers of a fragment, computed syntactically by the reference's table. -/
def props : Ms → Props
  | .pk_k _ => ⟨false, true, true, true, true⟩
  | .pk_h _ => ⟨false, false, true, true, true⟩
  | .older _ => ⟨true, false, false, false, false⟩
  | .after _ => ⟨true, false, false, false, false⟩
  | .sha256 _ => ⟨false, true, true, true, true⟩
  | .hash256 _ => ⟨false, true, true, true, true⟩
  | .ripemd160 _ => ⟨false, true, true, true, true⟩
  | .hash160 _ => ⟨false, true, true, true, true⟩
  | .and_v x y =>
    let px := props x; let py := props y
    ⟨px.z && py.z, (px.z && py.o) || (px.o && py.z), px.n || (px.z && py.n), false, py.u⟩
  | .and_b x y =>
    let px := props x; let py := props y
    ⟨px.z && py.z, (px.z && py.o) || (px.o && py.z), px.n || (px.z && py.n), px.d && py.d, true⟩
  | .or_b x z =>
    let px := props x; let pz := props z
    ⟨px.z && pz.z, (px.z && pz.o) || (px.o && pz.z), false, true, true⟩
  | .or_c x z =>
    let px := props x; let pz := props z
    ⟨px.z && pz.z, px.o && pz.z, false, false, false⟩
  | .or_d x z =>
    let px := props x; let pz := props z
    ⟨px.z && pz.z, px.o && pz.z, false, pz.d, pz.u⟩
  | .or_i x z =>
    let px := props x; let pz := props z
    ⟨false, px.z && pz.z, false, px.d || pz.d, px.u && pz.u⟩
  | .andor x y z =>
    let px := props x; let py := props y; let pz := props z
    ⟨px.z && py.z && pz.z, (px.z && py.o && pz.o) || (px.o && py.z && pz.z), false, pz.d, py.u && pz.u⟩
  | .multi _ _ => ⟨false, false, true, true, true⟩
  | .wrap_a x => let px := props x; ⟨false, false, false, px.d, px.u⟩
  | .wrap_s x => let px := props x; ⟨false, px.o, false, px.d, px.u⟩
  | .wrap_c x => let px := props x; ⟨false, px.o, px.n, px.d, true⟩
  | .wrap_d _ => ⟨false, true, true, true, false⟩
  | .wrap_v x => let px := props x; ⟨px.z, px.o, px.n, false, false⟩
  | .wrap_j x => let px := props x; ⟨false, px.o, true, true, px.u⟩
  | .wrap_n x => let px := props x; ⟨px.z, px.o, px.n, px.d, true⟩

/-- The typing rules of the reference's correctness table, with the resource facts the
translation needs (pushed data within `MAX_SCRIPT_ELEMENT_SIZE`, time-lock operands in
`1 … 2^31 - 1`, at most `MAX_PUBKEYS_PER_MULTISIG` keys). -/
inductive HasType : Ms → Ty → Prop
  | pk_k (key : Bytes) : key.length ≤ MAX_SCRIPT_ELEMENT_SIZE → HasType (.pk_k key) .K
  | pk_h (h : Bytes) : h.length ≤ MAX_SCRIPT_ELEMENT_SIZE → HasType (.pk_h h) .K
  | older (n : Int) : 1 ≤ n → n < 2 ^ 31 → HasType (.older n) .B
  | after (n : Int) : 1 ≤ n → n < 2 ^ 31 → HasType (.after n) .B
  | sha256 (h : Bytes) : h.length ≤ MAX_SCRIPT_ELEMENT_SIZE → HasType (.sha256 h) .B
  | hash256 (h : Bytes) : h.length ≤ MAX_SCRIPT_ELEMENT_SIZE → HasType (.hash256 h) .B
  | ripemd160 (h : Bytes) : h.length ≤ MAX_SCRIPT_ELEMENT_SIZE → HasType (.ripemd160 h) .B
  | hash160 (h : Bytes) : h.length ≤ MAX_SCRIPT_ELEMENT_SIZE → HasType (.hash160 h) .B
  | and_v {x y : Ms} {ty : Ty} : HasType x .V → HasType y ty → ty ≠ .W → HasType (.and_v x y) ty
  | and_b {x y : Ms} : HasType x .B → HasType y .W → HasType (.and_b x y) .B
  | or_b {x z : Ms} : HasType x .B → (props x).d = true → HasType z .W → (props z).d = true →
      HasType (.or_b x z) .B
  | or_c {x z : Ms} : HasType x .B → (props x).d = true → (props x).u = true → HasType z .V →
      HasType (.or_c x z) .V
  | or_d {x z : Ms} : HasType x .B → (props x).d = true → (props x).u = true → HasType z .B →
      HasType (.or_d x z) .B
  | or_i {x z : Ms} {ty : Ty} : HasType x ty → HasType z ty → ty ≠ .W → HasType (.or_i x z) ty
  | andor {x y z : Ms} {ty : Ty} : HasType x .B → (props x).d = true → (props x).u = true →
      HasType y ty → HasType z ty → ty ≠ .W → HasType (.andor x y z) ty
  | multi (k : Nat) (keys : List Bytes) : 1 ≤ k → k ≤ keys.length →
      keys.length ≤ MAX_PUBKEYS_PER_MULTISIG → (∀ key ∈ keys, key.length ≤ MAX_SCRIPT_ELEMENT_SIZE) →
      HasType (.multi k keys) .B
  | wrap_a {x : Ms} : HasType x .B → HasType (.wrap_a x) .W
  | wrap_s {x : Ms} : HasType x .B → (props x).o = true → HasType (.wrap_s x) .W
  | wrap_c {x : Ms} : HasType x .K → HasType (.wrap_c x) .B
  | wrap_d {x : Ms} : HasType x .V → (props x).z = true → HasType (.wrap_d x) .B
  | wrap_v {x : Ms} : HasType x .B → HasType (.wrap_v x) .V
  | wrap_j {x : Ms} : HasType x .B → (props x).n = true → HasType (.wrap_j x) .B
  | wrap_n {x : Ms} : HasType x .B → HasType (.wrap_n x) .B

/-- A decidable type checker for `HasType`: the type of a well-typed fragment, `none` otherwise
(`typeOf_sound` in the solutions shows `typeOf m = some ty → HasType m ty`). -/
def typeOf : Ms → Option Ty
  | .pk_k key => if key.length ≤ MAX_SCRIPT_ELEMENT_SIZE then some .K else none
  | .pk_h h => if h.length ≤ MAX_SCRIPT_ELEMENT_SIZE then some .K else none
  | .older n => if 1 ≤ n ∧ n < 2 ^ 31 then some .B else none
  | .after n => if 1 ≤ n ∧ n < 2 ^ 31 then some .B else none
  | .sha256 h => if h.length ≤ MAX_SCRIPT_ELEMENT_SIZE then some .B else none
  | .hash256 h => if h.length ≤ MAX_SCRIPT_ELEMENT_SIZE then some .B else none
  | .ripemd160 h => if h.length ≤ MAX_SCRIPT_ELEMENT_SIZE then some .B else none
  | .hash160 h => if h.length ≤ MAX_SCRIPT_ELEMENT_SIZE then some .B else none
  | .and_v x y =>
    match typeOf x, typeOf y with
    | some .V, some ty => if ty ≠ .W then some ty else none
    | _, _ => none
  | .and_b x y =>
    match typeOf x, typeOf y with
    | some .B, some .W => some .B
    | _, _ => none
  | .or_b x z =>
    match typeOf x, typeOf z with
    | some .B, some .W => if (props x).d && (props z).d then some .B else none
    | _, _ => none
  | .or_c x z =>
    match typeOf x, typeOf z with
    | some .B, some .V => if (props x).d && (props x).u then some .V else none
    | _, _ => none
  | .or_d x z =>
    match typeOf x, typeOf z with
    | some .B, some .B => if (props x).d && (props x).u then some .B else none
    | _, _ => none
  | .or_i x z =>
    match typeOf x, typeOf z with
    | some tx, some tz => if tx = tz ∧ tx ≠ .W then some tx else none
    | _, _ => none
  | .andor x y z =>
    match typeOf x, typeOf y, typeOf z with
    | some .B, some ty, some tz =>
      if (props x).d && (props x).u && decide (ty = tz) && decide (ty ≠ .W) then some ty else none
    | _, _, _ => none
  | .multi k keys =>
    if 1 ≤ k ∧ k ≤ keys.length ∧ keys.length ≤ MAX_PUBKEYS_PER_MULTISIG ∧
        keys.all (fun key => key.length ≤ MAX_SCRIPT_ELEMENT_SIZE) then some .B else none
  | .wrap_a x => match typeOf x with | some .B => some .W | _ => none
  | .wrap_s x => match typeOf x with | some .B => if (props x).o then some .W else none | _ => none
  | .wrap_c x => match typeOf x with | some .K => some .B | _ => none
  | .wrap_d x => match typeOf x with | some .V => if (props x).z then some .B else none | _ => none
  | .wrap_v x => match typeOf x with | some .B => some .V | _ => none
  | .wrap_j x => match typeOf x with | some .B => if (props x).n then some .B else none | _ => none
  | .wrap_n x => match typeOf x with | some .B => some .B | _ => none

/-! ### Satisfaction semantics -/

/-- `Sem f o m w out`: the witness `w` (top first) drives the fragment `m` to the output `out`,
the stack elements the translated script leaves above the untouched stack below: `[v]` for a `B`
or `W` fragment (`v` nonzero for a satisfaction, `[]` for a dissatisfaction), `[]` for a `V`
fragment, `[key, sig]` for a `K` fragment. This is the reference's satisfaction and
dissatisfaction table in one relation; the non-canonical combinations the script also accepts
(both sides of an `or_b` satisfied, a selector other than `1`) are included. -/
def Sem (f : Flags) (o : Oracle) : Ms → List Bytes → List Bytes → Prop
  | .pk_k key, w, out => ∃ sig, w = [sig] ∧ out = [key, sig]
  | .pk_h h, w, out => ∃ key sig, w = [key, sig] ∧ o.hash160 key = h ∧ out = [key, sig]
  | .older n, w, out => w = [] ∧ CsvPasses f o n ∧ out = [serialize n]
  | .after n, w, out => w = [] ∧ CltvPasses f o n ∧ out = [serialize n]
  | .sha256 h, w, out => ∃ pre, w = [pre] ∧ pre.length = 32 ∧ out = [boolBytes (decide (o.sha256 pre = h))]
  | .hash256 h, w, out => ∃ pre, w = [pre] ∧ pre.length = 32 ∧ out = [boolBytes (decide (o.hash256 pre = h))]
  | .ripemd160 h, w, out => ∃ pre, w = [pre] ∧ pre.length = 32 ∧ out = [boolBytes (decide (o.ripemd160 pre = h))]
  | .hash160 h, w, out => ∃ pre, w = [pre] ∧ pre.length = 32 ∧ out = [boolBytes (decide (o.hash160 pre = h))]
  | .and_v x y, w, out => ∃ wx wy, w = wx ++ wy ∧ Sem f o x wx [] ∧ Sem f o y wy out
  | .and_b x y, w, out => ∃ wx wy vx vy, w = wx ++ wy ∧ Sem f o x wx [vx] ∧ Sem f o y wy [vy] ∧
      out = [boolBytes (castToBool vx && castToBool vy)]
  | .or_b x z, w, out => ∃ wx wz vx vz, w = wx ++ wz ∧ Sem f o x wx [vx] ∧ Sem f o z wz [vz] ∧
      out = [boolBytes (castToBool vx || castToBool vz)]
  | .or_c x z, w, out => out = [] ∧ ∃ wx vx, Sem f o x wx [vx] ∧
      ((castToBool vx = true ∧ w = wx) ∨ (castToBool vx = false ∧ ∃ wz, w = wx ++ wz ∧ Sem f o z wz []))
  | .or_d x z, w, out => ∃ wx vx, Sem f o x wx [vx] ∧
      ((castToBool vx = true ∧ w = wx ∧ out = [vx]) ∨
       (castToBool vx = false ∧ ∃ wz, w = wx ++ wz ∧ Sem f o z wz out))
  | .or_i x z, w, out => ∃ b w', w = b :: w' ∧
      ((castToBool b = true ∧ Sem f o x w' out) ∨ (castToBool b = false ∧ Sem f o z w' out))
  | .andor x y z, w, out => ∃ wx vx, Sem f o x wx [vx] ∧
      ((castToBool vx = true ∧ ∃ wy, w = wx ++ wy ∧ Sem f o y wy out) ∨
       (castToBool vx = false ∧ ∃ wz, w = wx ++ wz ∧ Sem f o z wz out))
  | .multi k keys, w, out => ∃ sigs dummy ok, w = sigs ++ [dummy] ∧ sigs.length = k ∧
      multisigLoop o sigs keys.reverse = some ok ∧ (f.nulldummy = true → dummy = []) ∧ out = [boolBytes ok]
  | .wrap_a x, w, out => Sem f o x w out
  | .wrap_s x, w, out => Sem f o x w out
  | .wrap_c x, w, out => ∃ key sig ok, Sem f o x w [key, sig] ∧ o.checkSig sig key = some ok ∧ out = [boolBytes ok]
  | .wrap_d x, w, out => (w = [[1]] ∧ Sem f o x [] [] ∧ out = [[1]]) ∨ (w = [[]] ∧ out = [[]])
  | .wrap_v x, w, out => ∃ v, Sem f o x w [v] ∧ castToBool v = true ∧ out = []
  | .wrap_j x, w, out => (∃ e w', w = e :: w' ∧ e ≠ [] ∧ e.length ≤ MAX_SCRIPT_ELEMENT_SIZE ∧ Sem f o x w out) ∨
      (w = [[]] ∧ out = [[]])
  | .wrap_n x, w, out => ∃ v, Sem f o x w [v] ∧ out = [boolBytes (castToBool v)]

/-- Satisfaction of a `B` (or `W`) fragment: some output value that `CastToBool` accepts. -/
def Sat (f : Flags) (o : Oracle) (m : Ms) (w : List Bytes) : Prop :=
  ∃ v, Sem f o m w [v] ∧ castToBool v = true

/-- Dissatisfaction of a `B` (or `W`) fragment: the output is exactly the empty element. -/
def Dsat (f : Flags) (o : Oracle) (m : Ms) (w : List Bytes) : Prop := Sem f o m w [[]]

/-- Satisfaction of a `V` fragment: nothing is left. -/
def SatV (f : Flags) (o : Oracle) (m : Ms) (w : List Bytes) : Prop := Sem f o m w []

/-- The values a `B` or `W` fragment can leave: the script number of some `n` in
`0 … 2^31 - 1` (so a valid 4-byte `CScriptNum`; `[]` is `0`, `[1]` is `1`). -/
def GoodVal (v : Bytes) : Prop := ∃ n : Int, 0 ≤ n ∧ n < 2 ^ 31 ∧ v = serialize n

/-! ### Sequential execution -/

/-- The instruction loop of `EvalScript` without the final unbalanced-conditional check, so
that it composes sequentially. -/
def runSeq (f : Flags) (o : Oracle) : State → Script → Option State
  | s, [] => some s
  | s, i :: rest =>
    match step f o s i with
    | none => none
    | some s' => runSeq f o s' rest

end BitcoinMiniscript


