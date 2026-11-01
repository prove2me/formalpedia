-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P82
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P82
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:04:47.511411+00:00
-- url     : https://prove2.me/theorems/268e93c4-c0e9-44d8-8b52-c48d966f4d9c
-- title:
--   Definitions for A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits
-- statement:
--   The objects the formalized statements of *A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits* (arXiv:1206.3223) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SameGate`: Equality in PSU(2), using unitary representatives; §II, PDF p.2.
--   - `Syllable`: The two distinct syntax letters TH and SH; §II, PDF p.2.
--   - `syllableMatrix`: Matrices of the two syllables, modulo the source's scalar phases; p.2.
--   - `syllableValue`: Printed-order evaluation, including the empty identity word; p.2.
--   - `BsNormalized`: Empty or ending in TH, with no two consecutive SH letters; p.2.
--   - `BsCanonical`: No SH earlier than syllable five, counting from the left; p.2.
--   - `bsTCount`: Charged non-Clifford cost: SH contributes zero, TH contributes one; p.2.
--   - `BsCliffordLetter`: Clifford spelling alphabet, used only for a fixed table; Appendix A, p.8.
--   - `bsCliffordLetterMatrix`: U(2) representatives of the projective Clifford generators; pp.2,8.
--   - `cliffordWords`: All 24 projective Clifford representatives, in the source's G0,...,G23 order; Appendix A, PDF p.8. A terminal is a table index, not an arbitrary spelling.
--   - `cliffordMatrix`: Matrix of the actual retained Clifford terminal; Appendix A, p.8.
--   - `BsHTLetter`: Literal source input alphabet for Propositions 1--4; p.2.
--   - `htValue`: Evaluation of an input gate list, in printed order; pp.2,8.
--   - `CTLetter`: The cost model of §IV: an arbitrary Clifford is free, T costs one; pp.1--3.
--   - `ctValue`: Evaluation of a competing Clifford/T presentation; pp.2--3,6.
--   - `chargedT`: Actual count of non-Clifford T tokens, without expanding S; pp.1--3,6.
--   - `NormalOutput`: Returned leading-H flag, syllable body and Clifford terminal; Proposition 1, p.2.
--   - `bsNormalValue`: Exact value of a normalized presentation; Proposition 1, p.2.
--   - `CanonicalOutput`: Returned left Clifford, canonical core and right Clifford; Proposition 2, p.2.
--   - `canonicalValue`: The full presentation is evaluated, but is not claimed unique; pp.2--3.
--   - `BsStackSymbol`: Fixed machine alphabet: 0=H, 1=T, 2=S, 3=TH, 4=SH, 5..28=G0..G23, 29/30=false/true flags, 31=separator; Appendices C,D.
--   - `cliffordSymbol`: One table entry is a constant-size symbol; Appendix A, p.8.
--   - `syllableSymbols`: Serialization retains syllable syntax, not its gate expansion; p.2.
--   - `htSymbols`: Input encoding is a single list scan; Appendix C, p.8.
--   - `normalSymbols`: Actual normalized output encoding, with both flag and terminal retained; p.8.
--   - `canonicalSymbols`: Actual canonical output encoding, with both Clifford terminals retained; p.9.
--   - `StackAction`: Primitive unit-cost stack actions: unchanged tail is shared; Appendix C, p.8.
--   - `Instruction`: Each instruction tests only four heads and the finite control state; p.8.
--   - `Program`: A fixed finite symbolic procedure, chosen before all inputs; pp.8--9.
--   - `BsConfiguration`: Configuration with four finite stacks; none means halted; pp.8--9.
--   - `applyAction`: Constant-cost action, including pop on an empty work stack; p.8.
--   - `lookup`: Fully scanned fixed lookup table, with first matching instruction selected; all comparisons concern finite control and four finite symbols, not matrices.
--   - `bsMachineStep`: One actual transition; a missing row halts without silently changing output.
--   - `bsMachineRun`: Fuel counts transitions of this concrete procedure; pp.8--9.
--   - `bsInitial`: Initial state 0, input on stack 0 and three empty work stacks.
--   - `BsExecutes`: Operational execution and charge: full finite-table scan at each step, constant head/stack work, input setup, and the complete retained output. The factor 20 pays for four head inspections, tests and stack actions. Fuel beyond early halting is charged too, so it cannot undercount execution.
--   - `LinearNormalizes`: Uniform operational linear normalization, including the empty input; Propositions 1,3 and Appendix C, pp.2,3,8.
--   - `QuadraticReduces`: Quadratic phase starts from an already retained normalized presentation; Proposition 4, Appendix D, pp.3,8--9.
--   - `gateDistance`: Phase-insensitive trace distance, with division outside the square root; §IV, p.4.
--   - `hUnit`: A U(2) representative of H as an invertible matrix; §II, p.2.
--   - `sUnit`: A U(2) representative of S as an invertible matrix; §II, p.2.
--   - `ProjectiveMatrices`: Ambient projective matrix group. On the unitary subgroup generated here, quotienting by the center identifies precisely one unit scalar phase; p.2.
--   - `cliffordSubgroup`: The source's projective subgroup generated by H and S; §II, p.2.
--   - `BsSphereVector`: Cartesian coordinates for the trace-level sphere; §IV, pp.4--5.
--   - `unitSphere`: The unit two-sphere, before its positive-trace SU(2) parametrization; p.4.
--   - `bsPauli`: Fixed ordered Pauli basis X,Y,Z, matching the source's axes; pp.4,9.
--   - `sphereGate`: Unique positive-trace representative at 0<t<2, in the source's sphere coordinates; §IV, p.4. Degenerate endpoints are deliberately excluded by the theorem.
--   - `bsCliffordRotation`: Matrix of Clifford conjugation in the ordered Pauli basis; §IV p.4, Appendix E p.9.
--   - `octahedronVertices`: Six vertices of the source's octahedron; p.4.
--   - `octahedronRotations`: Rotational octahedral group as concrete matrices, excluding all reflections; p.4.
--   - `fundamentalTile`: Closed spherical triangle with vertices +X,+Z,+(1,1,1)/sqrt(3); p.4.
--   - `fundamentalInterior`: Interior relative to the two-sphere, not the ambient three-space; p.4.
--   - `tile`: The 24 tile images under conjugation; p.4.
--   - `tileInterior`: Images of the relative interiors; p.4.
--   - `initialVertices`: Vertices of the initial triangle, with the positive diagonal normalized; p.4.
--   - `tileVertices`: All tile vertices, as the union of images of the three initial vertices; p.5.
--   - `RecursionTree`: A supplied tree of the auxiliary choices in Eq.(1), §V, PDF p.5. Each node composes V W V-dagger W-dagger U. No approximation property of the auxiliary choices is assumed or claimed here.
--   - `recursionValue`: Exact five-factor gate at each node of Eq.(1); p.5.
--   - `LeavesBounded`: Every leaf is an actual canonical database entry of T-count at most t; p.5.
-- source:
--   A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits, arXiv:1206.3223v1, https://arxiv.org/abs/1206.3223v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates

/-!
Bocharov--Svore, arXiv:1206.3223v1. Products are in printed order,
acting right to left. Frozen H,T,S matrices are U(2) representatives of
exactly the source's projective gates: source H = i H_frozen and source
T = exp(-i*pi/8) T_frozen. Every gate equality below discards one unit
scalar phase. No state, measurement, ancilla or literal S=TT cost is used.

The local finite four-stack machine gives operational meaning to symbolic
runtime. Its transitions inspect four heads and use a fixed finite table;
only push/pop/keep operations are allowed. Setup and the actual returned
serialization are charged. No matrix arithmetic is assigned unit cost.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P82

open scoped BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-- Equality in PSU(2), using unitary representatives; §II, PDF p.2. -/
def SameGate (U V : Mat) : Prop := ∃ z : ℂ, ‖z‖ = 1 ∧ U = z • V

/-- The two distinct syntax letters TH and SH; §II, PDF p.2. -/
inductive Syllable where
  | th | sh
  deriving DecidableEq

/-- Matrices of the two syllables, modulo the source's scalar phases; p.2. -/
def syllableMatrix : Syllable → Mat
  | .th => QAlgorithms.gateT * QAlgorithms.hadamard
  | .sh => QAlgorithms.phaseS * QAlgorithms.hadamard

/-- Printed-order evaluation, including the empty identity word; p.2. -/
def syllableValue (w : List Syllable) : Mat := (w.map syllableMatrix).prod

/-- Empty or ending in TH, with no two consecutive SH letters; p.2. -/
def BsNormalized : List Syllable → Prop
  | [] => True
  | [.th] => True
  | [.sh] => False
  | a :: b :: w => (a ≠ .sh ∨ b ≠ .sh) ∧ BsNormalized (b :: w)

/-- No SH earlier than syllable five, counting from the left; p.2. -/
def BsCanonical (w : List Syllable) : Prop :=
  BsNormalized w ∧ ∀ a ∈ w.take 4, a = .th

/-- Charged non-Clifford cost: SH contributes zero, TH contributes one; p.2. -/
def bsTCount (w : List Syllable) : ℕ :=
  (w.filter fun a => decide (a = .th)).length

/-- Clifford spelling alphabet, used only for a fixed table; Appendix A, p.8. -/
inductive BsCliffordLetter where
  | h | s
  deriving DecidableEq

/-- U(2) representatives of the projective Clifford generators; pp.2,8. -/
def bsCliffordLetterMatrix : BsCliffordLetter → Mat
  | .h => QAlgorithms.hadamard
  | .s => QAlgorithms.phaseS

/-- All 24 projective Clifford representatives, in the source's G0,...,G23 order;
Appendix A, PDF p.8. A terminal is a table index, not an arbitrary spelling. -/
def cliffordWords : Fin 24 → List BsCliffordLetter := ![
  [], [.h], [.h,.s,.s,.h], [.s,.s], [.s], [.s,.s,.s],
  [.h,.s,.s], [.s,.s,.h], [.s,.h], [.s,.s,.s,.h],
  [.s,.s,.h,.s,.s,.h], [.s,.h,.s,.s,.h], [.s,.s,.s,.h,.s,.s,.h],
  [.h,.s], [.h,.s,.s,.s], [.s,.s,.h,.s,.s], [.s,.h,.s,.s],
  [.s,.s,.s,.h,.s,.s], [.h,.s,.h], [.h,.s,.s,.s,.h],
  [.h,.s,.h,.s,.s,.h], [.h,.s,.s,.s,.h,.s,.s,.h],
  [.s,.s,.s,.h,.s], [.s,.h,.s,.s,.s]]

/-- Matrix of the actual retained Clifford terminal; Appendix A, p.8. -/
def cliffordMatrix (g : Fin 24) : Mat :=
  ((cliffordWords g).map bsCliffordLetterMatrix).prod

/-- Literal source input alphabet for Propositions 1--4; p.2. -/
inductive BsHTLetter where
  | h | t
  deriving DecidableEq

/-- Evaluation of an input gate list, in printed order; pp.2,8. -/
def htValue (w : List BsHTLetter) : Mat :=
  (w.map fun a => match a with
    | .h => QAlgorithms.hadamard
    | .t => QAlgorithms.gateT).prod

/-- The cost model of §IV: an arbitrary Clifford is free, T costs one; pp.1--3. -/
inductive CTLetter where
  | clifford (g : Fin 24)
  | t
  deriving DecidableEq

/-- Evaluation of a competing Clifford/T presentation; pp.2--3,6. -/
def ctValue (w : List CTLetter) : Mat :=
  (w.map fun a => match a with
    | .clifford g => cliffordMatrix g
    | .t => QAlgorithms.gateT).prod

/-- Actual count of non-Clifford T tokens, without expanding S; pp.1--3,6. -/
def chargedT (w : List CTLetter) : ℕ :=
  (w.filter fun a => match a with | .t => true | .clifford _ => false).length

/-- Returned leading-H flag, syllable body and Clifford terminal; Proposition 1, p.2. -/
structure NormalOutput where
  leadingH : Bool
  body : List Syllable
  terminal : Fin 24

/-- Exact value of a normalized presentation; Proposition 1, p.2. -/
def bsNormalValue (o : NormalOutput) : Mat :=
  (if o.leadingH then QAlgorithms.hadamard else 1) *
    syllableValue o.body * cliffordMatrix o.terminal

/-- Returned left Clifford, canonical core and right Clifford; Proposition 2, p.2. -/
structure CanonicalOutput where
  left : Fin 24
  body : List Syllable
  right : Fin 24

/-- The full presentation is evaluated, but is not claimed unique; pp.2--3. -/
def canonicalValue (o : CanonicalOutput) : Mat :=
  cliffordMatrix o.left * syllableValue o.body * cliffordMatrix o.right

/-- Fixed machine alphabet: 0=H, 1=T, 2=S, 3=TH, 4=SH,
5..28=G0..G23, 29/30=false/true flags, 31=separator; Appendices C,D. -/
abbrev BsStackSymbol := Fin 32

/-- One table entry is a constant-size symbol; Appendix A, p.8. -/
def cliffordSymbol (g : Fin 24) : BsStackSymbol := ⟨5 + g.val, by omega⟩

/-- Serialization retains syllable syntax, not its gate expansion; p.2. -/
def syllableSymbols (w : List Syllable) : List BsStackSymbol :=
  w.map fun a => match a with | .th => 3 | .sh => 4

/-- Input encoding is a single list scan; Appendix C, p.8. -/
def htSymbols (w : List BsHTLetter) : List BsStackSymbol :=
  w.map fun a => match a with | .h => 0 | .t => 1

/-- Actual normalized output encoding, with both flag and terminal retained; p.8. -/
def normalSymbols (o : NormalOutput) : List BsStackSymbol :=
  [if o.leadingH then 30 else 29] ++ syllableSymbols o.body ++ [cliffordSymbol o.terminal]

/-- Actual canonical output encoding, with both Clifford terminals retained; p.9. -/
def canonicalSymbols (o : CanonicalOutput) : List BsStackSymbol :=
  [cliffordSymbol o.left] ++ syllableSymbols o.body ++ [cliffordSymbol o.right]

/-- Primitive unit-cost stack actions: unchanged tail is shared; Appendix C, p.8. -/
inductive StackAction where
  | keep | pop | push (a : BsStackSymbol)

/-- Each instruction tests only four heads and the finite control state; p.8. -/
structure Instruction where
  state : ℕ
  heads : Fin 4 → Option BsStackSymbol
  actions : Fin 4 → StackAction
  next : Option ℕ

/-- A fixed finite symbolic procedure, chosen before all inputs; pp.8--9. -/
abbrev Program := List Instruction

/-- Configuration with four finite stacks; none means halted; pp.8--9. -/
structure BsConfiguration where
  control : Option ℕ
  workStacks : Fin 4 → List BsStackSymbol

/-- Constant-cost action, including pop on an empty work stack; p.8. -/
def applyAction : StackAction → List BsStackSymbol → List BsStackSymbol
  | .keep, s => s
  | .pop, s => s.tail
  | .push a, s => a :: s

/-- Fully scanned fixed lookup table, with first matching instruction selected;
all comparisons concern finite control and four finite symbols, not matrices. -/
def lookup (p : Program) (c : BsConfiguration) : Option Instruction :=
  p.foldr (fun row rest =>
    if c.control = some row.state ∧ (fun j => (c.workStacks j).head?) = row.heads
    then some row else rest) none

/-- One actual transition; a missing row halts without silently changing output. -/
def bsMachineStep (p : Program) (c : BsConfiguration) : BsConfiguration :=
  if c.control = none then c else
    match lookup p c with
    | none => { c with control := none }
    | some row => ⟨row.next, fun j => applyAction (row.actions j) (c.workStacks j)⟩

/-- Fuel counts transitions of this concrete procedure; pp.8--9. -/
def bsMachineRun (p : Program) : ℕ → BsConfiguration → BsConfiguration
  | 0, c => c
  | k + 1, c => bsMachineRun p k (bsMachineStep p c)

/-- Initial state 0, input on stack 0 and three empty work stacks. -/
def bsInitial (input : List BsStackSymbol) : BsConfiguration :=
  ⟨some 0, fun j => if j = 0 then input else []⟩

/-- Operational execution and charge: full finite-table scan at each step,
constant head/stack work, input setup, and the complete retained output.
The factor 20 pays for four head inspections, tests and stack actions.
Fuel beyond early halting is charged too, so it cannot undercount execution. -/
def BsExecutes (p : Program) (input output : List BsStackSymbol) (cost : ℕ) : Prop :=
  ∃ steps : ℕ,
    (bsMachineRun p steps (bsInitial input)).control = none ∧
    (bsMachineRun p steps (bsInitial input)).workStacks 0 = output ∧
    cost = input.length + output.length + 1 + 20 * (p.length + 1) * steps

/-- Uniform operational linear normalization, including the empty input;
Propositions 1,3 and Appendix C, pp.2,3,8. -/
def LinearNormalizes (p : Program) (K : ℕ) : Prop :=
  ∀ w : List BsHTLetter, ∃ o : NormalOutput, ∃ cost : ℕ,
    BsNormalized o.body ∧ SameGate (bsNormalValue o) (htValue w) ∧
    BsExecutes p (htSymbols w) (normalSymbols o) cost ∧ cost ≤ K * (w.length + 1)

/-- Quadratic phase starts from an already retained normalized presentation;
Proposition 4, Appendix D, pp.3,8--9. -/
def QuadraticReduces (p : Program) (K : ℕ) : Prop :=
  ∀ o : NormalOutput, BsNormalized o.body → ∃ c : CanonicalOutput, ∃ cost : ℕ,
    BsCanonical c.body ∧ SameGate (canonicalValue c) (bsNormalValue o) ∧
    BsExecutes p (normalSymbols o) (canonicalSymbols c) cost ∧
    cost ≤ K * (bsTCount o.body + 1) ^ 2

/-- Phase-insensitive trace distance, with division outside the square root; §IV, p.4. -/
def gateDistance (U V : Mat) : ℝ :=
  Real.sqrt (2 - ‖Matrix.trace (U * star V)‖) / 2

/-- A U(2) representative of H as an invertible matrix; §II, p.2. -/
def hUnit : Matˣ where
  val := QAlgorithms.hadamard
  inv := QAlgorithms.hadamard
  val_inv := QAlgorithms.hadamard_mul_self
  inv_val := QAlgorithms.hadamard_mul_self

/-- A U(2) representative of S as an invertible matrix; §II, p.2. -/
def sUnit : Matˣ where
  val := QAlgorithms.phaseS
  inv := QAlgorithms.phaseS ^ 3
  val_inv := by
    ext a b
    cases a <;> cases b <;>
      simp [QAlgorithms.phaseS, pow_succ, Matrix.mul_apply, Fintype.sum_bool]
  inv_val := by
    ext a b
    cases a <;> cases b <;>
      simp [QAlgorithms.phaseS, pow_succ, Matrix.mul_apply, Fintype.sum_bool]

/-- Ambient projective matrix group. On the unitary subgroup generated here,
quotienting by the center identifies precisely one unit scalar phase; p.2. -/
abbrev ProjectiveMatrices := Matˣ ⧸ Subgroup.center Matˣ

/-- The source's projective subgroup generated by H and S; §II, p.2. -/
def cliffordSubgroup : Subgroup ProjectiveMatrices :=
  Subgroup.closure {QuotientGroup.mk hUnit, QuotientGroup.mk sUnit}

example : syllableValue [] = 1 := rfl

example : BsNormalized [] ∧ BsCanonical [] ∧ bsTCount [] = 0 := by
  simp [BsNormalized, BsCanonical, bsTCount]

example : BsCanonical [.th, .th, .th, .th, .sh, .th] ∧
    bsTCount [.th, .th, .th, .th, .sh, .th] = 5 := by
  simp [BsCanonical, BsNormalized, bsTCount]

example : ¬ BsNormalized [.sh, .sh, .th] := by simp [BsNormalized]

example : chargedT [.clifford 4] = 0 ∧ cliffordMatrix 4 = QAlgorithms.phaseS := by
  simp [chargedT, cliffordMatrix, cliffordWords, bsCliffordLetterMatrix]

example : SameGate (1 : Mat) 1 := ⟨1, by simp, by simp⟩

example : (bsMachineRun [] 1 (bsInitial [])).control = none := by
  simp [bsMachineRun, bsMachineStep, lookup, bsInitial]

example : normalSymbols ⟨false, [], 0⟩ = [29, 5] := rfl

example : canonicalSymbols ⟨0, [], 0⟩ = [5, 5] := rfl

example : QuotientGroup.mk hUnit ∈ cliffordSubgroup := by
  exact Subgroup.subset_closure (by simp)

example : gateDistance (1 : Mat) 1 = 0 := by
  norm_num [gateDistance, Matrix.trace, Fintype.sum_bool]

/-- Cartesian coordinates for the trace-level sphere; §IV, pp.4--5. -/
abbrev BsSphereVector := Fin 3 → ℝ

/-- The unit two-sphere, before its positive-trace SU(2) parametrization; p.4. -/
def unitSphere : Set BsSphereVector := {v | ∑ j, (v j) ^ 2 = 1}

/-- Fixed ordered Pauli basis X,Y,Z, matching the source's axes; pp.4,9. -/
def bsPauli : Fin 3 → Mat := ![QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ]

/-- Unique positive-trace representative at 0<t<2, in the source's sphere coordinates;
§IV, p.4. Degenerate endpoints are deliberately excluded by the theorem. -/
def sphereGate (t : ℝ) (v : BsSphereVector) : Mat :=
  ((t / 2 : ℝ) : ℂ) • (1 : Mat) +
    (Complex.I * (Real.sqrt (1 - t ^ 2 / 4) : ℂ)) •
      (∑ j, (v j : ℂ) • bsPauli j)

/-- Matrix of Clifford conjugation in the ordered Pauli basis; §IV p.4, Appendix E p.9. -/
def bsCliffordRotation (g : Fin 24) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (Matrix.trace
    (bsPauli i * cliffordMatrix g * bsPauli j * star (cliffordMatrix g))).re / 2

/-- Six vertices of the source's octahedron; p.4. -/
def octahedronVertices : Set BsSphereVector :=
  {v | ∃ j : Fin 3,
    v = (fun k => if k = j then 1 else 0) ∨
    v = (fun k => if k = j then -1 else 0)}

/-- Rotational octahedral group as concrete matrices, excluding all reflections; p.4. -/
def octahedronRotations : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {R | R.transpose * R = 1 ∧ R.det = 1 ∧
    (fun v => R.mulVec v) '' octahedronVertices = octahedronVertices}

/-- Closed spherical triangle with vertices +X,+Z,+(1,1,1)/sqrt(3); p.4. -/
def fundamentalTile : Set BsSphereVector :=
  {v | v ∈ unitSphere ∧ 0 ≤ v 1 ∧ v 1 ≤ v 0 ∧ v 1 ≤ v 2}

/-- Interior relative to the two-sphere, not the ambient three-space; p.4. -/
def fundamentalInterior : Set BsSphereVector :=
  {v | v ∈ unitSphere ∧ 0 < v 1 ∧ v 1 < v 0 ∧ v 1 < v 2}

/-- The 24 tile images under conjugation; p.4. -/
def tile (g : Fin 24) : Set BsSphereVector := (fun v => (bsCliffordRotation g).mulVec v) '' fundamentalTile

/-- Images of the relative interiors; p.4. -/
def tileInterior (g : Fin 24) : Set BsSphereVector :=
  (fun v => (bsCliffordRotation g).mulVec v) '' fundamentalInterior

/-- Vertices of the initial triangle, with the positive diagonal normalized; p.4. -/
def initialVertices : Set BsSphereVector :=
  {v | v = (fun k => if k = 0 then 1 else 0) ∨
    v = (fun k => if k = 2 then 1 else 0) ∨
    v = (fun _ => (Real.sqrt 3)⁻¹)}

/-- All tile vertices, as the union of images of the three initial vertices; p.5. -/
def tileVertices : Set BsSphereVector :=
  {v | ∃ g : Fin 24, ∃ w ∈ initialVertices, v = (bsCliffordRotation g).mulVec w}

example : (![1, 0, 0] : BsSphereVector) ∈ fundamentalTile := by
  have hthird : (![1, 0, 0] : BsSphereVector) 2 = 0 := rfl
  norm_num [fundamentalTile, unitSphere, Fin.sum_univ_three, hthird]

example : sphereGate 2 (fun _ => 0) = 1 := by
  norm_num [sphereGate]

/-- A supplied tree of the auxiliary choices in Eq.(1), §V, PDF p.5.
Each node composes V W V-dagger W-dagger U. No approximation property
of the auxiliary choices is assumed or claimed here. -/
inductive RecursionTree : ℕ → Type where
  | base (c : CanonicalOutput) : RecursionTree 0
  | step {n : ℕ} (v w u : RecursionTree n) : RecursionTree (n + 1)

/-- Exact five-factor gate at each node of Eq.(1); p.5. -/
def recursionValue : {n : ℕ} → RecursionTree n → Mat
  | _, .base c => canonicalValue c
  | _, .step v w u => recursionValue v * recursionValue w * star (recursionValue v) *
      star (recursionValue w) * recursionValue u

/-- Every leaf is an actual canonical database entry of T-count at most t; p.5. -/
def LeavesBounded (t : ℕ) : {n : ℕ} → RecursionTree n → Prop
  | _, .base c => BsCanonical c.body ∧ bsTCount c.body ≤ t
  | _, .step v w u => LeavesBounded t v ∧ LeavesBounded t w ∧ LeavesBounded t u

example (c : CanonicalOutput) : recursionValue (.base c) = canonicalValue c := rfl

end QAlgorithms.Papers.Independent.Intakenext100.P82


