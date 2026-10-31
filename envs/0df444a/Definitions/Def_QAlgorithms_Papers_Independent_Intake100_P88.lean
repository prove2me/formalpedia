-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88
-- name    : QAlgorithms_Papers_Independent_Intake100_P88
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T15:31:37.660395+00:00
-- url     : https://prove2.me/theorems/5cdfd54b-f18a-47da-9e5f-c391c303d010
-- title:
--   Definitions for Partition Algebras
-- statement:
--   The objects the formalized statements of *Partition Algebras* (arXiv:math/0401314) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Vertex`: The two rows of vertices; `false` is the top row (PDF pp.3--4).
--   - `PartitionDiagram`: A diagram is its set partition, independent of a drawing (PDF p.3, (1.1)).
--   - `upperVertex`: Place a vertex in the upper or lower diagram of a stack (PDF p.4).
--   - `lowerVertex`: Place a vertex in the lower diagram of a stack (PDF p.4).
--   - `outerVertex`: Retained outer vertices of a stack (PDF p.4).
--   - `stackEdge`: Edges coming from either factor, with the middle row identified (PDF p.4).
--   - `diagramCompose`: Stack the left factor above the right; discard middle-only blocks (PDF p.4).
--   - `propagatingNumber`: Blocks meeting both rows, counted without multiplicity (PDF p.3, (1.2)).
--   - `boundaryIndex`: Clockwise boundary order: top left-to-right, bottom right-to-left (PDF p.4).
--   - `IsPlanar`: Noncrossing set partitions in the boundary order, i.e. planar diagrams (PDF p.4).
--   - `IsPairing`: Every block has exactly two vertices (PDF p.4, Brauer diagrams).
--   - `IsPermutation`: A permutation diagram has one vertex from each row in every pair (PDF p.4).
--   - `permutationDiagram`: Permutation diagram of a bijection, with the named row convention (PDF p.4).
--   - `LevelDiagram`: Integer/half-integer level `m/2`, with the last pair joined at odd `m` (PDF p.3).
--   - `DiagramSpace`: The diagram vector space; no multiplication is assumed (PDF p.9).
--   - `IsOrbitBasis`: Coarsening-sum characterization of the orbit basis (PDF pp.9--10, corrected (2.3)).
--   - `diagramIndex`: Label a physical vertex; at odd levels the distinguished pair is fixed to `n` (PDF p.19).
--   - `partitionDiagramMatrix`: The actual equality-constraint matrix, including restriction at odd levels (PDF pp.18--19).
--   - `partitionDiagramAction`: Linear extension of the diagram action, without postulating algebra laws (PDF p.19, (3.3)).
--   - `simultaneousValuePermutation`: Simultaneous permutation of every tensor-basis index (PDF p.19, (3.7)).
--   - `blockNumber`: Number of all blocks, including the distinguished block at odd levels (PDF p.19).
--   - `precedingDiagram`: Canonical diagram inclusion from the preceding half-step (PDF p.9, (2.2)). When the physical rank increases, the new top/bottom pair forms a new block; when it is unchanged, the original relation is retained.
--   - `precedingGenerator`: The generator `p_(m/2)` in its physical diagram space (PDF p.6, (1.10)). At even `m` it isolates the last pair; at odd `m ≥ 3` it merges the last two columns. The statement using it requires `m ≥ 2`, so no undefined `p_(1/2)` is used.
--   - `deficientDiagrams`: The actual deficient-propagation diagram set (PDF pp.4,11, (1.4), (2.10)). At odd levels the distinguished block is included in the physical count.
--   - `principalLeftIdeal`: The left ideal `Ap`, expressed as the fixed points of right multiplication (PDF p.16).
--   - `StableLabel`: Stable Young labels at doubled level `m` (PDF p.13, (2.23)).
--   - `TensorLabel`: Finite-parameter labels: partitions of `n` or `n-1` (PDF p.21, (3.21)).
--   - `stableEdge`: Edges in the stable graph: stay/remove, then stay/add (PDF p.13).
--   - `tensorEdge`: Edges in the tensor-space graph: remove, then add one box (PDF p.21).
--   - `traceCoefficient`: Integer-level trace coefficient polynomial, explicitly (3.24), PDF p.23.
--   - `halfTraceCoefficient`: Half-level coefficient, including the unnormalized closure factor `n` (PDF p.23).
--   - `levelTraceCoefficient`: Select the coefficient polynomial by level parity (PDF pp.23--24).
--   - `coefficientRoots`: Union of zero sets over all labels, not the roots of each individual coefficient.
--   - `transpositionSum`: Sum of all transpositions in the group algebra (PDF p.25, (3.28)).
--   - `contentSum`: Sum of box contents, using the source convention `column - row` (PDF pp.27,31).
--   - `splitMatrixUnit`: A matrix unit in a fixed split decomposition (PDF pp.35--37, (4.23), (4.31)).
--   - `splitTrace`: A trace expanded in the irreducible matrix characters (PDF p.37, (4.31)).
--   - `edgeMatrix`: Coordinate inclusion of one branching-edge copy, including its multiplicity (PDF pp.35--36).
--   - `TraceNondegenerate`: Nondegeneracy excludes the zero test vector (PDF p.39, proof of Lemma 5.1).
--   - `traceGram`: The Gram matrix of the actual trace product form (PDF p.39).
--   - `IsTraceDualBasis`: A trace-dual basis, with the same index set (PDF pp.39--40).
--   - `algebraAverage`: Algebra trace averaging, with the actual dual basis (PDF p.40).
--   - `moduleAverage`: Module trace averaging; both sides are actions, not algebra multiplication (PDF p.40).
--   - `IrreducibleAction`: Irreducibility for an explicitly given commuting action (PDF pp.41--42). This is the invariant-subspace formulation of simplicity, including nonzero space.
--   - `regularTrace`: Trace of actual left multiplication on the regular representation (PDF p.43).
-- source:
--   Partition Algebras, arXiv:math/0401314v2, https://arxiv.org/abs/math/0401314v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SpechtModules
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P65
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30

/-!
Statements from Halverson--Ram, Partition Algebras, arXiv:math/0401314v2.
Levels are doubled natural numbers. No weighted partition-algebra structure is
postulated: results needing that additional construction are explicitly deferred.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)
open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- The two rows of vertices; `false` is the top row (PDF pp.3--4). -/
abbrev Vertex (k : ℕ) := Bool × Fin k

/-- A diagram is its set partition, independent of a drawing (PDF p.3, (1.1)). -/
abbrev PartitionDiagram (k : ℕ) := Setoid (Vertex k)

instance diagramFinite (k : ℕ) : Finite (PartitionDiagram k) := by
  apply Finite.of_injective (fun d : PartitionDiagram k => d.r)
  intro d e h
  exact Setoid.ext fun a b => Iff.of_eq (congrFun (congrFun h a) b)

/-- Place a vertex in the upper or lower diagram of a stack (PDF p.4). -/
def upperVertex {k : ℕ} (a : Vertex k) : Fin 3 × Fin k :=
  (if a.1 then 1 else 0, a.2)

/-- Place a vertex in the lower diagram of a stack (PDF p.4). -/
def lowerVertex {k : ℕ} (a : Vertex k) : Fin 3 × Fin k :=
  (if a.1 then 2 else 1, a.2)

/-- Retained outer vertices of a stack (PDF p.4). -/
def outerVertex {k : ℕ} (a : Vertex k) : Fin 3 × Fin k :=
  (if a.1 then 2 else 0, a.2)

/-- Edges coming from either factor, with the middle row identified (PDF p.4). -/
def stackEdge {k : ℕ} (d e : PartitionDiagram k) (a b : Fin 3 × Fin k) : Prop :=
  (∃ c f : Vertex k, upperVertex c = a ∧ upperVertex f = b ∧ d c f) ∨
  (∃ c f : Vertex k, lowerVertex c = a ∧ lowerVertex f = b ∧ e c f)

/-- Stack the left factor above the right; discard middle-only blocks (PDF p.4). -/
def diagramCompose {k : ℕ} (d e : PartitionDiagram k) : PartitionDiagram k :=
  Setoid.ker (fun a => Quotient.mk (Relation.EqvGen.setoid (stackEdge d e)) (outerVertex a))

example (d e : PartitionDiagram 0) : diagramCompose d e = d := by
  apply Setoid.ext
  intro a _
  exact Fin.elim0 a.2

/-- Blocks meeting both rows, counted without multiplicity (PDF p.3, (1.2)). -/
def propagatingNumber {k : ℕ} (d : PartitionDiagram k) : ℕ :=
  Nat.card {c : Quotient d //
    (∃ i : Fin k, Quotient.mk d (false, i) = c) ∧
    (∃ i : Fin k, Quotient.mk d (true, i) = c)}

/-- Clockwise boundary order: top left-to-right, bottom right-to-left (PDF p.4). -/
def boundaryIndex {k : ℕ} (a : Vertex k) : ℕ :=
  if a.1 then 2 * k - 1 - a.2.val else a.2.val

/-- Noncrossing set partitions in the boundary order, i.e. planar diagrams (PDF p.4). -/
def IsPlanar {k : ℕ} (d : PartitionDiagram k) : Prop :=
  ∀ a b c f : Vertex k,
    boundaryIndex a < boundaryIndex b → boundaryIndex b < boundaryIndex c →
    boundaryIndex c < boundaryIndex f → d a c → d b f → d a b

/-- Every block has exactly two vertices (PDF p.4, Brauer diagrams). -/
def IsPairing {k : ℕ} (d : PartitionDiagram k) : Prop :=
  ∀ a : Vertex k, ∃ b : Vertex k, b ≠ a ∧ ∀ c : Vertex k, d a c ↔ c = a ∨ c = b

/-- A permutation diagram has one vertex from each row in every pair (PDF p.4). -/
def IsPermutation {k : ℕ} (d : PartitionDiagram k) : Prop :=
  IsPairing d ∧ ∀ a b : Vertex k, d a b → a.1 = b.1 → a = b

/-- Permutation diagram of a bijection, with the named row convention (PDF p.4). -/
def permutationDiagram {k : ℕ} (s : Equiv.Perm (Fin k)) : PartitionDiagram k :=
  Setoid.ker (fun a : Vertex k => if a.1 then s a.2 else a.2)

/-- Integer/half-integer level `m/2`, with the last pair joined at odd `m` (PDF p.3). -/
def LevelDiagram (m : ℕ) :=
  {d : PartitionDiagram ((m + 1) / 2) // m % 2 = 1 →
    ∀ i : Fin ((m + 1) / 2), i.val + 1 = (m + 1) / 2 → d (false, i) (true, i)}

instance levelDiagramFinite (m : ℕ) : Finite (LevelDiagram m) :=
  inferInstanceAs (Finite {d : PartitionDiagram ((m + 1) / 2) // _})

instance levelDiagramFintype (m : ℕ) : Fintype (LevelDiagram m) := Fintype.ofFinite _

/-- The diagram vector space; no multiplication is assumed (PDF p.9). -/
abbrev DiagramSpace (m : ℕ) := LevelDiagram m →₀ ℂ

example : (permutationDiagram (Equiv.refl (Fin 1))) (false, 0) (true, 0) := rfl

example : ¬ (permutationDiagram (Equiv.refl (Fin 2))) (false, 0) (true, 1) := by
  change (0 : Fin 2) ≠ 1
  intro h
  have hval := congrArg Fin.val h
  omega

/-- Coarsening-sum characterization of the orbit basis (PDF pp.9--10, corrected (2.3)). -/
def IsOrbitBasis (m : ℕ) (b : Module.Basis (LevelDiagram m) ℂ (DiagramSpace m)) : Prop :=
  ∀ d : LevelDiagram m,
    Finsupp.single d 1 = ∑ e ∈ Finset.univ.filter (fun e : LevelDiagram m => d.val ≤ e.val), b e

/-- Label a physical vertex; at odd levels the distinguished pair is fixed to `n` (PDF p.19). -/
def diagramIndex {n m : ℕ} (hn : 0 < n) (input output : TensorIndex n (m / 2))
    (a : Vertex ((m + 1) / 2)) : Fin n :=
  if h : a.2.val < m / 2 then
    if a.1 then output ⟨a.2.val, h⟩ else input ⟨a.2.val, h⟩
  else ⟨n - 1, by omega⟩

/-- The actual equality-constraint matrix, including restriction at odd levels (PDF pp.18--19). -/
def partitionDiagramMatrix {n m : ℕ} (hn : 0 < n) (d : LevelDiagram m) :
    Matrix (TensorIndex n (m / 2)) (TensorIndex n (m / 2)) ℂ := fun output input =>
  if ∀ a c : Vertex ((m + 1) / 2), d.val a c →
    diagramIndex hn input output a = diagramIndex hn input output c then 1 else 0

/-- Linear extension of the diagram action, without postulating algebra laws (PDF p.19, (3.3)). -/
def partitionDiagramAction {n m : ℕ} (hn : 0 < n) :
    DiagramSpace m →ₗ[ℂ] Matrix (TensorIndex n (m / 2)) (TensorIndex n (m / 2)) ℂ :=
  Finsupp.linearCombination ℂ (partitionDiagramMatrix (m := m) hn)

/-- Simultaneous permutation of every tensor-basis index (PDF p.19, (3.7)). -/
def simultaneousValuePermutation {n m : ℕ} (s : Equiv.Perm (Fin n)) :
    Matrix (TensorIndex n (m / 2)) (TensorIndex n (m / 2)) ℂ := fun output input =>
  if output = fun i => s (input i) then 1 else 0

/-- Number of all blocks, including the distinguished block at odd levels (PDF p.19). -/
def blockNumber {m : ℕ} (d : LevelDiagram m) : ℕ := Nat.card (Quotient d.val)

example {n m : ℕ} (hn : 0 < n) (d : LevelDiagram m) :
    partitionDiagramAction hn (Finsupp.single d 1) = partitionDiagramMatrix hn d := by
  simp [partitionDiagramAction]

/-- Canonical diagram inclusion from the preceding half-step (PDF p.9, (2.2)).
When the physical rank increases, the new top/bottom pair forms a new block;
when it is unchanged, the original relation is retained. -/
def precedingDiagram (m : ℕ) (d : LevelDiagram (m - 1)) : PartitionDiagram ((m + 1) / 2) :=
  Setoid.ker (fun a : Vertex ((m + 1) / 2) =>
    if h : a.2.val < ((m - 1) + 1) / 2 then
      some (Quotient.mk d.val (a.1, ⟨a.2.val, h⟩)) else none)

/-- The generator `p_(m/2)` in its physical diagram space (PDF p.6, (1.10)).
At even `m` it isolates the last pair; at odd `m ≥ 3` it merges the last two columns.
The statement using it requires `m ≥ 2`, so no undefined `p_(1/2)` is used. -/
def precedingGenerator (m : ℕ) : PartitionDiagram ((m + 1) / 2) :=
  if m % 2 = 0 then
    Setoid.ker (fun a : Vertex ((m + 1) / 2) =>
      if a.2.val + 1 = (m + 1) / 2 then (Sum.inl a.1 : Bool ⊕ Fin ((m + 1) / 2))
      else Sum.inr a.2)
  else
    Setoid.ker (fun a : Vertex ((m + 1) / 2) =>
      if (m + 1) / 2 ≤ a.2.val + 2 then none else some a.2)

/-- The actual deficient-propagation diagram set (PDF pp.4,11, (1.4), (2.10)).
At odd levels the distinguished block is included in the physical count. -/
def deficientDiagrams (m : ℕ) : Set (LevelDiagram m) :=
  {d | propagatingNumber d.val < (m + 1) / 2}

example : ¬ precedingGenerator 2 (false, 0) (true, 0) := by
  change (Sum.inl false : Bool ⊕ Fin 1) ≠ Sum.inl true
  simp

example : precedingGenerator 3 (false, 0) (true, 1) := rfl

/-- The left ideal `Ap`, expressed as the fixed points of right multiplication (PDF p.16). -/
def principalLeftIdeal {A : Type u} [Ring A] (p : A) : Submodule A A where
  carrier := {a | a * p = a}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; change (a + b) * p = a + b; rw [add_mul, ha, hb]
  smul_mem' := by intro a b hb; change (a * b) * p = a * b; rw [mul_assoc, hb]

example {A : Type u} [Ring A] (a : A) : a ∈ principalLeftIdeal (1 : A) := by
  change a * 1 = a
  exact mul_one a

/-- Stable Young labels at doubled level `m` (PDF p.13, (2.23)). -/
abbrev StableLabel (m : ℕ) := {mu : YoungDiagram // mu.card ≤ m / 2}

/-- Finite-parameter labels: partitions of `n` or `n-1` (PDF p.21, (3.21)). -/
abbrev TensorLabel (n m : ℕ) :=
  {lam : YoungDiagram // lam.card = n - m % 2 ∧ lam.card - lam.rowLen 0 ≤ m / 2}

/-- Edges in the stable graph: stay/remove, then stay/add (PDF p.13). -/
def stableEdge (m : ℕ) (lam mu : YoungDiagram) : Prop :=
  if m % 2 = 0 then mu = lam ∨ (mu ≤ lam ∧ lam.card = mu.card + 1)
  else mu = lam ∨ (lam ≤ mu ∧ mu.card = lam.card + 1)

/-- Edges in the tensor-space graph: remove, then add one box (PDF p.21). -/
def tensorEdge (m : ℕ) (lam mu : YoungDiagram) : Prop :=
  if m % 2 = 0 then mu ≤ lam ∧ lam.card = mu.card + 1
  else lam ≤ mu ∧ mu.card = lam.card + 1

example : stableEdge 0 (⊥ : YoungDiagram) ⊥ := by simp [stableEdge]

/-- Integer-level trace coefficient polynomial, explicitly (3.24), PDF p.23. -/
def traceCoefficient (mu : YoungDiagram) : Polynomial ℂ :=
  Polynomial.C (∏ b ∈ mu.cells, (1 / (hookLength mu b.1 b.2 : ℂ))) *
    ∏ j ∈ Finset.range mu.card,
      (Polynomial.X - Polynomial.C ((mu.card : ℂ) + (mu.rowLen j : ℂ) - ((j + 1 : ℕ) : ℂ)))

/-- Half-level coefficient, including the unnormalized closure factor `n` (PDF p.23). -/
def halfTraceCoefficient (mu : YoungDiagram) : Polynomial ℂ :=
  Polynomial.X * (traceCoefficient mu).comp (Polynomial.X - 1)

/-- Select the coefficient polynomial by level parity (PDF pp.23--24). -/
def levelTraceCoefficient (m : ℕ) (mu : YoungDiagram) : Polynomial ℂ :=
  if m % 2 = 0 then traceCoefficient mu else halfTraceCoefficient mu

/-- Union of zero sets over all labels, not the roots of each individual coefficient. -/
def coefficientRoots (m : ℕ) : Set ℂ :=
  {z | ∃ mu : StableLabel m, (levelTraceCoefficient m mu.val).eval z = 0}

example : traceCoefficient (⊥ : YoungDiagram) = 1 := by
  simp [traceCoefficient, YoungDiagram.card]

example : halfTraceCoefficient (⊥ : YoungDiagram) = Polynomial.X := by
  simp [halfTraceCoefficient, traceCoefficient, YoungDiagram.card]

/-- Sum of all transpositions in the group algebra (PDF p.25, (3.28)). -/
def transpositionSum (n : ℕ) : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
    MonoidAlgebra.single (Equiv.swap i j) 1

/-- Sum of box contents, using the source convention `column - row` (PDF pp.27,31). -/
def contentSum (mu : YoungDiagram) : ℂ :=
  ∑ b ∈ mu.cells, ((b.2 : ℂ) - (b.1 : ℂ))

example : transpositionSum 0 = 0 := by simp [transpositionSum]

/-- A matrix unit in a fixed split decomposition (PDF pp.35--37, (4.23), (4.31)). -/
def splitMatrixUnit {F A I : Type*} [Field F] [Ring A] [Algebra F A]
    [Fintype I] [DecidableEq I] (dim : I → ℕ)
    (e : A ≃ₐ[F] ((i : I) → Matrix (Fin (dim i)) (Fin (dim i)) F))
    (mu : I) (p q : Fin (dim mu)) : A :=
  e.symm (Pi.single mu (Matrix.single p q 1))

/-- A trace expanded in the irreducible matrix characters (PDF p.37, (4.31)). -/
def splitTrace {F A I : Type*} [Field F] [Ring A] [Algebra F A]
    [Fintype I] (dim : I → ℕ)
    (e : A ≃ₐ[F] ((i : I) → Matrix (Fin (dim i)) (Fin (dim i)) F))
    (coeff : I → F) (a : A) : F := ∑ i, coeff i * (e a i).trace

/-- Coordinate inclusion of one branching-edge copy, including its multiplicity (PDF pp.35--36). -/
def edgeMatrix {F : Type*} [Field F] {a b : ℕ} (j : Fin a ↪ Fin b) :
    Matrix (Fin b) (Fin a) F := fun r p => if r = j p then 1 else 0

example {F A I : Type*} [Field F] [Ring A] [Algebra F A] [Fintype I]
    (dim : I → ℕ) (e : A ≃ₐ[F] ((i : I) → Matrix (Fin (dim i)) (Fin (dim i)) F))
    (c : I → F) : splitTrace dim e c 0 = 0 := by simp [splitTrace]

example {F : Type*} [Field F] (n : ℕ) :
    edgeMatrix (F := F) (Function.Embedding.refl (Fin n)) = 1 := by
  ext i j
  simp [edgeMatrix, Matrix.one_apply]

/-- Nondegeneracy excludes the zero test vector (PDF p.39, proof of Lemma 5.1). -/
def TraceNondegenerate {F A : Type*} [Zero F] [Zero A] [Mul A] (t : A → F) : Prop :=
  ∀ b : A, b ≠ 0 → ∃ a : A, t (b * a) ≠ 0

/-- The Gram matrix of the actual trace product form (PDF p.39). -/
def traceGram {F A I : Type*} [Field F] [Ring A] [Algebra F A]
    (t : A →ₗ[F] F) (b : Module.Basis I F A) : Matrix I I F := fun i j => t (b i * b j)

/-- A trace-dual basis, with the same index set (PDF pp.39--40). -/
def IsTraceDualBasis {F A I : Type*} [Field F] [Ring A] [Algebra F A] [DecidableEq I]
    (t : A →ₗ[F] F) (b c : Module.Basis I F A) : Prop :=
  ∀ i j : I, t (b i * c j) = if i = j then 1 else 0

/-- Algebra trace averaging, with the actual dual basis (PDF p.40). -/
def algebraAverage {F A I : Type*} [Field F] [Ring A] [Algebra F A] [Fintype I]
    (b c : Module.Basis I F A) (a : A) : A := ∑ i, b i * a * c i

/-- Module trace averaging; both sides are actions, not algebra multiplication (PDF p.40). -/
def moduleAverage {F A I M N : Type*} [Field F] [Ring A] [Algebra F A] [Fintype I]
    [AddCommGroup M] [AddCommGroup N] [Module F M] [Module F N]
    [Module A M] [Module A N] (b c : Module.Basis I F A) (phi : M →ₗ[F] N) (m : M) : N :=
  ∑ i, b i • phi (c i • m)

example {F A I : Type*} [Field F] [Ring A] [Algebra F A] [Fintype I]
    (b c : Module.Basis I F A) : algebraAverage b c (0 : A) = 0 := by
  simp [algebraAverage]

example {F A I M N : Type*} [Field F] [Ring A] [Algebra F A] [Fintype I]
    [AddCommGroup M] [AddCommGroup N] [Module F M] [Module F N]
    [Module A M] [Module A N] (b c : Module.Basis I F A) (m : M) :
    moduleAverage b c (0 : M →ₗ[F] N) m = 0 := by
  simp [moduleAverage]

example {F : Type*} [Field F] : TraceNondegenerate (fun a : F => a) := by
  intro b hb
  exact ⟨1, by simpa using hb⟩

/-- Irreducibility for an explicitly given commuting action (PDF pp.41--42).
This is the invariant-subspace formulation of simplicity, including nonzero space. -/
def IrreducibleAction {F Z V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (act : Z → V → V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule F V,
    (∀ z v, v ∈ W → act z v ∈ W) → W = ⊥ ∨ W = ⊤

example {F : Type*} [Field F] : IrreducibleAction (F := F) (fun a v : F => a * v) := by
  refine ⟨inferInstance, ?_⟩
  intro W _
  exact eq_bot_or_eq_top W

/-- Trace of actual left multiplication on the regular representation (PDF p.43). -/
def regularTrace {F A : Type*} [Field F] [Ring A] [Algebra F A]
    [FiniteDimensional F A] (a : A) : F :=
  LinearMap.trace F A (Algebra.lmul F A a)

example {F A : Type*} [Field F] [Ring A] [Algebra F A]
    [FiniteDimensional F A] : regularTrace (F := F) (0 : A) = 0 := by
  simp [regularTrace]

end QAlgorithms.Papers.Independent.Intake100.P88


