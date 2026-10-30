-- Prove2me | Definitions.Def_QAlgorithms_Defs_Complexity
-- name    : QAlgorithms_Defs_Complexity
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T11:15:34.060227+00:00
-- url     : https://prove2.me/theorems/2a7fe538-1662-48a8-9ed7-937cfa782ff1
-- title:
--   prove2quantum library: Defs.Complexity
-- statement:
--   Shared definitions of the prove2quantum Lean library (`QAlgorithms.Defs.Complexity`), reused by its paper formalizations.
--
--   - `Str`: Copied from `PvsNP.Str` (Cook, p.2): a binary string `w ∈ Σ*` with `Σ = {0,1}`. Used by de Wolf p.122 (§13.2) for languages and reductions.
--   - `PolyTimeComputable`: Copied from `PvsNP.PolyTimeComputable` (Cook, Definition 3); de Wolf p.122 (§13.2), p.187 (§20.3): a function `f : Σ* → Σ*` is polynomial-time computable: a multi-stack machine started with `w` on its input stack halts within `p(|w|)` steps with `f w` on its output stack, for some polynomial `p`.
--   - `Bits`: Copied from `ShiShallow.Bits`.
--   - `QState`: Copied from `ShiShallow.QState`: a raw amplitude vector on `n` qubits.
--   - `hMat`: Copied from `ShiShallow.hMat`: the Hadamard gate.
--   - `sMat`: Copied from `ShiShallow.sMat`: the phase gate `diag(1, i)`.
--   - `tMat`: Copied from `ShiShallow.tMat`: the `T` gate `diag(1, e^{iπ/4})`.
--   - `xMat`: Copied from `ShiShallow.xMat`: the bit-flip gate.
--   - `apply1`: Copied from `ShiShallow.apply1`: one-qubit gate on wire `i`; equals `I ⊗ ⋯ ⊗ U ⊗ ⋯ ⊗ I` with `U`'s row index on the output wire.
--   - `cnotState`: Copied from `ShiShallow.cnotState`: CNOT with control `i`, target `j`.
--   - `Instr`: Copied from `ShiShallow.Instr`: the instructions `H, S, T, X, CNOT`.
--   - `Instr.apply`: Copied from `ShiShallow.Instr.apply`.
--   - `Instr.support`: Copied from `ShiShallow.Instr.support`: the wires an instruction touches.
--   - `Layered`: Copied from `ShiShallow.Layered`; de Wolf p.123 (§13.3), p.127 (Definition 1): a layered circuit, a list of layers, each a list of instructions.
--   - `depth`: Copied from `ShiShallow.depth`: the number of layers.
--   - `LayerOk`: Copied from `ShiShallow.LayerOk`: a layer's gates act on pairwise disjoint wires.
--   - `runLayer`: Copied from `ShiShallow.runLayer`.
--   - `runLayered`: Copied from `ShiShallow.runLayered`.
--   - `Family`: Copied from `ShiClass.Family`; de Wolf p.123 (§13.3), p.127 (Definition 1): a quantum circuit family: for each input length `n`, a number of ancilla wires beyond a mandatory first one, a layered circuit on `n + (anc n + 1)` wires, and a designated output wire.
--   - `encNat`: Copied from `ShiBQP.encNat`: a natural number in unary, terminated by `false`.
--   - `encStr`: Copied from `ShiBQP.encStr`: a list of binary strings, length-prefixed and concatenated.
--   - `encInstr`: Copied from `ShiBQP.encInstr`: an instruction as a constructor tag followed by its wires.
--   - `encLayer`: Copied from `ShiBQP.encLayer`.
--   - `encCirc`: Copied from `ShiBQP.encCirc`.
--   - `encFamilyAt`: Copied from `ShiBQP.encFamilyAt`: the ancilla count, output wire and circuit at length `n`.
--   - `unary`: Copied from `ShiBQP.unary`: the unary encoding `1^n`.
--   - `Uniform`: Copied from `ShiBQP.Uniform`; de Wolf p.123 (footnote 1): classical polynomial-time uniformity: a polynomial-time computable map sends `1^n` to the code of the family at length `n`.
--   - `WellFormed`: Copied from `ShiBQP.WellFormed`: every layer of every circuit acts on disjoint wires.
--   - `PolyBounded`: Copied from `ShiBQP.PolyBounded`: one polynomial bounds the depth and the ancilla count.
--   - `toBits`: Copied from `ShiBQP.toBits`: a binary string read as an input of its own length.
--   - `QMAFamily`: Copied from `ShiClassQMA.QMAFamily`; de Wolf p.127 (Definition 1: "a uniform family `{C_n}` of polynomial-size quantum circuits with two input registers and one output qubit, and a polynomial `w`"): at input length `n` the verifier acts on `n` input wires, `wit n` witness wires and `anc n + 1` ancilla/output wires.
--   - `QMAFamily.toFamily`: Copied from `ShiClassQMA.QMAFamily.toFamily`: the witness block folded into the ancillas.
--   - `witnessInputState`: Copied from `ShiClassQMA.witnessInputState`: input `x`, witness `ψ`, ancillas zero.
--   - `Normalized`: Copied from `ShiClassQMA.Normalized`: a witness is a unit vector.
--   - `QMAFamily.acceptWith`: Copied from `ShiClassQMA.QMAFamily.acceptWith`: the probability that the output wire reads `1` on input `x` with witness `ψ`.
--   - `PromiseProblem`: de Wolf p.127 (§14.1: "A promise problem `L` partitions the set `{0,1}*` of all binary strings into `L_1`, `L_0`, and `L_*`"): the yes-instances `L_1` and no-instances `L_0` (disjoint); `L_*` is the rest, on which nothing is required.
--   - `PromiseQMA`: de Wolf p.127 (Definition 1): the promise problems in QMA: some uniform, well-formed, polynomially bounded verifier family accepts every `x ∈ L_1` with some normalized witness with probability `≥ 2/3`, and every `x ∈ L_0` with every normalized witness with probability `≤ 1/3`. This is `ShiClassQMA.QMA` with "`w ∈ L` / `w ∉ L`" replaced by "`w ∈ L_1` / `w ∈ L_0`".
--   - `PromiseReduces`: de Wolf p.122 (§13.2: "there exists a polynomial-time computable function `f` such that `x ∈ L′` iff `f(x) ∈ L`"), adapted to promise problems as used in §14.3: a polynomial-time Karp reduction maps yes-instances to yes-instances and no-instances to no-instances.
--   - `QMAHard`: de Wolf p.130 (§14.3: "any other problem in QMA can be reduced to it"): `L` is QMA-hard.
--   - `QMAComplete`: de Wolf p.130 (§14.3): `L` is QMA-complete: in QMA and QMA-hard.
-- source:
--   prove2quantum Lean library, module QAlgorithms.Defs.Complexity

import Definitions.Def_QAlgorithms_Defs_LinearSystems
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAlgorithms_ClassicalStringListEncoding

-- Str, encNat, PolyTimeComputable, unary, encStr: identical copies already published on Prove2Me; imported instead of re-declared

/-!
# Complexity classes (shared definition layer)

Verbatim copies, with provenance, of this repository's audited definitions, so that chunks can use
them without depending on the `bqp-pp` and `qma-amplification` projects (the algorithms workspace
requires only Mathlib; trap Q14):

* `Str`, `PolyTimeComputable` from `bqp-pp/src/Definitions/Def_PvsNP.lean` (Cook's Definition 3,
  machine model `Turing.FinTM2`);
* the layered Clifford+T circuits of `bqp-pp/src/Definitions/Def_ShiShallow_Core.lean`;
* `Family` from `bqp-pp/src/Definitions/Def_ShiClass_Core.lean` and the uniformity, well-formedness
  and size bounds of `bqp-pp/src/Definitions/Def_ShiBQP_Core.lean`;
* `QMAFamily`, `witnessInputState`, `Normalized`, `acceptWith` from
  `qma-amplification/Definitions/Def_ShiClassQMA.lean`.

The only new objects are de Wolf's promise problems (§14.1, Definition 1), the promise version of
`ShiClassQMA.QMA`, Karp reductions between promise problems, QMA-hardness and QMA-completeness.
-/

namespace QAlgorithms.Complexity

open Computability Turing

/-! ### From `Def_PvsNP.lean` -/

/-! ### From `Def_ShiShallow_Core.lean` (verbatim) -/

/-- Copied from `ShiShallow.Bits`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- Copied from `ShiShallow.QState`: a raw amplitude vector on `n` qubits. -/
abbrev QState (n : ℕ) := Bits n → ℂ

/-- Copied from `ShiShallow.hMat`: the Hadamard gate. -/
noncomputable def hMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a && b then -(Real.sqrt 2)⁻¹ else (Real.sqrt 2)⁻¹

/-- Copied from `ShiShallow.sMat`: the phase gate `diag(1, i)`. -/
noncomputable def sMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a = b then (if a then Complex.I else 1) else 0

/-- Copied from `ShiShallow.tMat`: the `T` gate `diag(1, e^{iπ/4})`. -/
noncomputable def tMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    if a = b then (if a then Complex.exp (Complex.I * Real.pi / 4) else 1) else 0

/-- Copied from `ShiShallow.xMat`: the bit-flip gate. -/
noncomputable def xMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a = b then 0 else 1

/-- Copied from `ShiShallow.apply1`: one-qubit gate on wire `i`; equals `I ⊗ ⋯ ⊗ U ⊗ ⋯ ⊗ I` with
`U`'s row index on the output wire. -/
noncomputable def apply1 {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n) :
    QState n :=
  fun x => ∑ b : Bool, U (x i) b * ψ (Function.update x i b)

/-- Copied from `ShiShallow.cnotState`: CNOT with control `i`, target `j`. -/
def cnotState {n : ℕ} (i j : Fin n) (_hij : i ≠ j) (ψ : QState n) : QState n :=
  fun x => ψ (Function.update x j (xor (x j) (x i)))

/-- Copied from `ShiShallow.Instr`: the instructions `H, S, T, X, CNOT`. -/
inductive Instr (n : ℕ) where
  | h (i : Fin n)
  | s (i : Fin n)
  | t (i : Fin n)
  | x (i : Fin n)
  | cnot (i j : Fin n) (hij : i ≠ j)

/-- Copied from `ShiShallow.Instr.apply`. -/
noncomputable def Instr.apply {n : ℕ} : Instr n → QState n → QState n
  | .h i => apply1 hMat i
  | .s i => apply1 sMat i
  | .t i => apply1 tMat i
  | .x i => apply1 xMat i
  | .cnot i j hij => cnotState i j hij

/-- Copied from `ShiShallow.Instr.support`: the wires an instruction touches. -/
def Instr.support {n : ℕ} : Instr n → Finset (Fin n)
  | .h i => {i}
  | .s i => {i}
  | .t i => {i}
  | .x i => {i}
  | .cnot i j _ => {i, j}

/-- Copied from `ShiShallow.Layered`; de Wolf p.123 (§13.3), p.127 (Definition 1): a layered
circuit, a list of layers, each a list of instructions. -/
abbrev Layered (n : ℕ) := List (List (Instr n))

/-- Copied from `ShiShallow.depth`: the number of layers. -/
def depth {n : ℕ} (c : Layered n) : ℕ := c.length

/-- Copied from `ShiShallow.LayerOk`: a layer's gates act on pairwise disjoint wires. -/
def LayerOk {n : ℕ} (l : List (Instr n)) : Prop :=
  l.Pairwise fun a b => Disjoint a.support b.support

/-- Copied from `ShiShallow.runLayer`. -/
noncomputable def runLayer {n : ℕ} (l : List (Instr n)) (ψ : QState n) : QState n :=
  l.foldl (fun st g => g.apply st) ψ

/-- Copied from `ShiShallow.runLayered`. -/
noncomputable def runLayered {n : ℕ} (c : Layered n) (ψ : QState n) : QState n :=
  c.foldl (fun st l => runLayer l st) ψ

/-! ### From `Def_ShiClass_Core.lean` and `Def_ShiBQP_Core.lean` (verbatim) -/

/-- Copied from `ShiClass.Family`; de Wolf p.123 (§13.3), p.127 (Definition 1): a quantum circuit
family: for each input length `n`, a number of ancilla wires beyond a mandatory first one, a
layered circuit on `n + (anc n + 1)` wires, and a designated output wire. -/
structure Family where
  /-- Number of ancilla wires at input length `n`, beyond a mandatory first one. -/
  anc : ℕ → ℕ
  /-- The circuit at input length `n`. -/
  circ : (n : ℕ) → Layered (n + (anc n + 1))
  /-- The output wire at input length `n`. -/
  out : (n : ℕ) → Fin (n + (anc n + 1))

/-- Copied from `ShiBQP.encInstr`: an instruction as a constructor tag followed by its wires. -/
def encInstr {m : ℕ} : Instr m → Str
  | .h i => encNat 0 ++ encNat (i : ℕ)
  | .s i => encNat 1 ++ encNat (i : ℕ)
  | .t i => encNat 2 ++ encNat (i : ℕ)
  | .x i => encNat 3 ++ encNat (i : ℕ)
  | .cnot i j _ => encNat 4 ++ encNat (i : ℕ) ++ encNat (j : ℕ)

/-- Copied from `ShiBQP.encLayer`. -/
def encLayer {m : ℕ} (l : List (Instr m)) : Str := encStr (l.map encInstr)

/-- Copied from `ShiBQP.encCirc`. -/
def encCirc {m : ℕ} (c : Layered m) : Str := encStr (c.map encLayer)

/-- Copied from `ShiBQP.encFamilyAt`: the ancilla count, output wire and circuit at length `n`. -/
def encFamilyAt (F : Family) (n : ℕ) : Str :=
  encNat (F.anc n) ++ encNat ((F.out n : ℕ)) ++ encCirc (F.circ n)

/-- Copied from `ShiBQP.Uniform`; de Wolf p.123 (footnote 1): classical polynomial-time
uniformity: a polynomial-time computable map sends `1^n` to the code of the family at length
`n`. -/
def Uniform (F : Family) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ n : ℕ, f (unary n) = encFamilyAt F n

/-- Copied from `ShiBQP.WellFormed`: every layer of every circuit acts on disjoint wires. -/
def WellFormed (F : Family) : Prop := ∀ (n : ℕ), ∀ l ∈ F.circ n, LayerOk l

/-- Copied from `ShiBQP.PolyBounded`: one polynomial bounds the depth and the ancilla count. -/
def PolyBounded (F : Family) : Prop :=
  ∃ q : Polynomial ℕ, (∀ n : ℕ, depth (F.circ n) ≤ q.eval n) ∧ (∀ n : ℕ, F.anc n ≤ q.eval n)

/-- Copied from `ShiBQP.toBits`: a binary string read as an input of its own length. -/
def toBits (w : Str) : Bits w.length := fun i => w.get i

/-! ### From `Def_ShiClassQMA.lean` (verbatim) -/

/-- Copied from `ShiClassQMA.QMAFamily`; de Wolf p.127 (Definition 1: "a uniform family `{C_n}` of
polynomial-size quantum circuits with two input registers and one output qubit, and a polynomial
`w`"): at input length `n` the verifier acts on `n` input wires, `wit n` witness wires and
`anc n + 1` ancilla/output wires. -/
structure QMAFamily where
  /-- Ancilla count beyond the mandatory output wire. -/
  anc : ℕ → ℕ
  /-- Witness-wire count at input length `n`. -/
  wit : ℕ → ℕ
  /-- The circuit at input length `n`. -/
  circ : (n : ℕ) → Layered (n + (wit n + (anc n + 1)))
  /-- The designated output wire at input length `n`. -/
  out : (n : ℕ) → Fin (n + (wit n + (anc n + 1)))

/-- Copied from `ShiClassQMA.QMAFamily.toFamily`: the witness block folded into the ancillas. -/
def QMAFamily.toFamily (F : QMAFamily) : Family where
  anc := fun n => F.wit n + F.anc n
  circ := F.circ
  out := F.out

/-- Copied from `ShiClassQMA.witnessInputState`: input `x`, witness `ψ`, ancillas zero. -/
def witnessInputState {n : ℕ} (F : QMAFamily) (x : Bits n) (ψ : QState (F.wit n)) :
    QState (n + (F.wit n + (F.anc n + 1))) :=
  fun y =>
    if (∀ i : Fin n, y (Fin.castAdd (F.wit n + (F.anc n + 1)) i) = x i) ∧
       (∀ l : Fin (F.anc n + 1), y (Fin.natAdd n (Fin.natAdd (F.wit n) l)) = false)
    then ψ (fun j : Fin (F.wit n) => y (Fin.natAdd n (Fin.castAdd (F.anc n + 1) j)))
    else 0

/-- Copied from `ShiClassQMA.Normalized`: a witness is a unit vector. -/
def Normalized {k : ℕ} (ψ : QState k) : Prop := ∑ z : Bits k, ‖ψ z‖ ^ 2 = 1

/-- Copied from `ShiClassQMA.QMAFamily.acceptWith`: the probability that the output wire reads `1`
on input `x` with witness `ψ`. -/
noncomputable def QMAFamily.acceptWith {n : ℕ} (F : QMAFamily) (x : Bits n)
    (ψ : QState (F.wit n)) : ℝ :=
  ∑ y : Bits (n + (F.wit n + (F.anc n + 1))),
    if y (F.out n) then ‖runLayered (F.circ n) (witnessInputState F x ψ) y‖ ^ 2 else 0

/-! ### Promise problems (new) -/

/-- de Wolf p.127 (§14.1: "A promise problem `L` partitions the set `{0,1}*` of all binary strings
into `L_1`, `L_0`, and `L_*`"): the yes-instances `L_1` and no-instances `L_0` (disjoint);
`L_*` is the rest, on which nothing is required. -/
structure PromiseProblem where
  /-- `L_1`. -/
  yes : Set Str
  /-- `L_0`. -/
  no : Set Str
  /-- `L_1 ∩ L_0 = ∅`. -/
  disjoint : Disjoint yes no

/-- de Wolf p.127 (Definition 1): the promise problems in QMA: some uniform, well-formed,
polynomially bounded verifier family accepts every `x ∈ L_1` with some normalized witness with
probability `≥ 2/3`, and every `x ∈ L_0` with every normalized witness with probability `≤ 1/3`.
This is `ShiClassQMA.QMA` with "`w ∈ L` / `w ∉ L`" replaced by "`w ∈ L_1` / `w ∈ L_0`". -/
def PromiseQMA : Set PromiseProblem :=
  {L | ∃ F : QMAFamily, Uniform F.toFamily ∧ WellFormed F.toFamily ∧ PolyBounded F.toFamily ∧
    ∀ w : Str,
      (w ∈ L.yes → ∃ ψ : QState (F.wit w.length), Normalized ψ ∧
          (2 : ℝ) / 3 ≤ F.acceptWith (toBits w) ψ) ∧
      (w ∈ L.no → ∀ ψ : QState (F.wit w.length), Normalized ψ →
          F.acceptWith (toBits w) ψ ≤ (1 : ℝ) / 3)}

/-- de Wolf p.122 (§13.2: "there exists a polynomial-time computable function `f` such that
`x ∈ L′` iff `f(x) ∈ L`"), adapted to promise problems as used in §14.3: a polynomial-time Karp
reduction maps yes-instances to yes-instances and no-instances to no-instances. -/
def PromiseReduces (L' L : PromiseProblem) : Prop :=
  ∃ r : Str → Str, PolyTimeComputable r ∧ (∀ x ∈ L'.yes, r x ∈ L.yes) ∧ (∀ x ∈ L'.no, r x ∈ L.no)

/-- de Wolf p.130 (§14.3: "any other problem in QMA can be reduced to it"): `L` is QMA-hard. -/
def QMAHard (L : PromiseProblem) : Prop :=
  ∀ L' ∈ PromiseQMA, PromiseReduces L' L

/-- de Wolf p.130 (§14.3): `L` is QMA-complete: in QMA and QMA-hard. -/
def QMAComplete (L : PromiseProblem) : Prop :=
  L ∈ PromiseQMA ∧ QMAHard L

/-! ### Sanity tests -/

/-- Every promise problem reduces to itself (when the identity map is polynomial-time). -/
example (L : PromiseProblem) (hid : PolyTimeComputable id) : PromiseReduces L L :=
  ⟨id, hid, fun _ hx => hx, fun _ hx => hx⟩

example : depth ([[], []] : Layered 2) = 2 := rfl

example : encNat 2 = [true, true, false] := rfl

/-- The empty circuit does nothing. -/
example {n : ℕ} (ψ : QState n) : runLayered ([] : Layered n) ψ = ψ := rfl

end QAlgorithms.Complexity


