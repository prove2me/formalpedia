-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P98
-- name    : QAlgorithms_Papers_Independent_Intake100_P98
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T16:03:10.776529+00:00
-- url     : https://prove2.me/theorems/44d4a33f-1846-4997-b653-8755356f2f3f
-- title:
--   Definitions for A polynomiality property for Littlewood-Richardson coefficients
-- statement:
--   The objects the formalized statements of *A polynomiality property for Littlewood-Richardson coefficients* (arXiv:math/0308101) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Coordinates`: Three blocks of padded coordinates, PDF pp.3,7. Blocks 0,1,2 are lambda,mu,nu.
--   - `paddedLRCoefficient`: The coefficient in padded coordinates, PDF p.3. Only dominant triples are used in statements. The frozen row-list diagram sorts the padded list; on these antitone inputs it preserves the specified partition. There is no determinant normalization.
--   - `IntegralDomain`: The source's integral parameter domain, PDF pp.3,7--8; empty partitions allowed.
--   - `SizeEquation`: The real size hyperplane, PDF pp.7--9.
--   - `RealDomain`: The real cone Upsilon from (34), PDF p.11, with dominant nonnegative coordinates.
--   - `realTriple`: Real realization of an integral triple, PDF pp.7--8.
--   - `stretch`: Integral dilation, (21), PDF p.6.
--   - `InteriorIndex`: Genuinely interior hive positions, the explicit range in (22), PDF p.6.
--   - `RhombusIndex`: Rhombus origins; the guard i+j+2<=k handles k=1 without Nat truncation. PDF p.6, (17)--(19). The product order fixes orientation before origin.
--   - `vertexCoefficient`: Coefficients of a hive vertex after the boundary substitution (20), PDF p.6. At corners use row zero first, then column zero, then the diagonal. The only alternative values meet at (k,0), where they agree on the size hyperplane.
--   - `rhombusCoefficient`: Left minus right of HC, with the sign chosen for <=0; (17)--(22), PDF p.6.
--   - `hiveMatrix`: Actual matrix E_k=[b|I], (23)--(24), PDF p.7. No equality to LR counts is a field of this construction.
--   - `boundaryMatrix`: Actual boundary matrix B_k, the negative boundary coefficients of HC, (22)--(24), PDF pp.6--7.
--   - `boundaryRhs`: Boundary right-hand side B_k x, PDF p.7, (25).
--   - `PointedKernel`: Nonnegative real kernel condition in Definition 1.4, PDF p.4.
--   - `partitionFiber`: Actual nonnegative integral fiber, Definition 1.4, PDF p.4.
--   - `vectorPartition`: Vector partition count, Definition 1.4, PDF p.4. Nat.card is used only with pointed kernels in theorem statements. The kernel condition is a conclusion for E_k, not an assumed matrix property.
--   - `columnCone`: Positive hull of a specified column set, including zero, PDF pp.4--5.
--   - `columnBases`: Column bases, PDF p.5. Cardinality and independence specify full row rank. The empty basis is allowed for the zero-row matrix (k=1).
--   - `chamberAt`: Cell at b: intersection of all basis cones containing b, PDF p.5. Taking these intersections and their faces is the common refinement, not an arbitrarily chosen polynomiality subdivision.
--   - `faces`: Exposed faces of a polyhedral cone, including the cone itself (ell=0). Used to retain all lattice boundary points, PDF pp.4--5.
--   - `partitionComplex`: The actual vector-partition chamber complex, common refinement of basis cones with all their faces, PDF p.5. Inputs outside column support create no cell.
--   - `lrComplex`: The LR complex of Definition 2.4, PDF pp.7--8. Pull back the actual E_k complex along B_k, then intersect with C_k^(1) and C_k^(2), retaining faces.
--   - `lrSupport`: Closed hive support, as the union of the constructed LR cones, PDF pp.7--8.
--   - `BlockDegreeAtMost`: Total degree inside EACH of the three coordinate blocks, PDF p.10, Theorem 4.1; not the maximum of individual-variable degrees.
--   - `evalReal`: Evaluation of a rational polynomial on real coordinates, PDF pp.9--11.
--   - `QuasipolynomialOn`: Positive common period and residue-class polynomials on the integral size hyperplane, Corollary 2.5, PDF p.8. Total degree uses the printed coarse bound.
--   - `PositiveRoot`: Positive roots e_i-e_j, PDF p.2, with zero-based i<j.
--   - `kostant`: Kostant's K, Definition 1.2, PDF p.3: a genuine count of root decompositions. This is finite: dotting with (k-1,k-2,...,0) bounds each nonnegative multiplicity.
--   - `rootHalfSum`: Half sum of positive roots, PDF p.3. Arithmetic is in R before subtracting.
--   - `permuteRootCoordinates`: sigma(e_i)=e_{sigma(i)}; coordinates therefore use sigma inverse, PDF p.3.
--   - `steinbergArgument`: Steinberg argument from (14), PDF p.4.
--   - `inversions`: Number of inversions in the usual order 0<...<k-1, PDF pp.3--4.
--   - `steinbergSum`: Actual alternating Kostant sum, (14), PDF p.4, with integer signs.
--   - `rootMatrix`: Positive roots written in simple-root coordinates, PDF p.5.
--   - `simpleCoordinates`: Coordinates in the simple-root basis on sum v_i=0, PDF pp.2,5.
--   - `kostantComplex`: Kostant chamber complex in the standard sum-zero realization, PDF pp.5,8.
--   - `rootInterior`: Interior relative to the root hyperplane, PDF pp.8--9.
--   - `kostantPiece`: Associated Kostant polynomial as in Definition 3.2, PDF p.9. This chooses only a Kostant piece from the standard piecewise-polynomial background (p.5), never a polynomial specified by LR values. The explicit zero fallback makes the construction total even on sets that are not Kostant chambers. Polynomials may differ off the root hyperplane, where they are never evaluated by the theorem.
--   - `kostantLabel`: Fixed chamber labels are the chamber sets themselves; `none` is label 0 outside support. Choosing among interiors is independent of LR coefficients. This avoids any dependence on an incidental integer numbering, PDF p.9.
--   - `permutationOrder`: A fixed total order on permutations, chosen once by a finite enumeration, Definition 3.2, PDF p.9. The sum itself is invariant under that enumeration.
--   - `steinbergType`: The type matrix indexed by the fixed finite permutation index set; Definition 3.2, PDF p.9. Reindexing a matrix by a total order changes no entries.
--   - `steinbergP`: P is computed by the alternating sum of associated Kostant pieces, (28), PDF p.9. No equality to LR coefficients is assumed in any definition.
--   - `fundamentalWeight`: Fundamental weight omega_(j+1), (6), PDF p.2. The index is Fin(k-1), correcting the nonexistent omega_k in (27), PDF p.9.
--   - `WallIndex`: Indices of all affine Steinberg walls, (27), PDF p.9.
--   - `wallValue`: Affine wall equation INCLUDING the delta shifts, (27)--(31), PDF pp.9--10.
--   - `steinbergRegion`: Open regions of the affine Steinberg arrangement in the size hyperplane, PDF p.9. All sign patterns are included; empty patterns are harmless.
--   - `sizeInterior`: Size-hyperplane relative interior, PDF pp.10--11.
--   - `LRGeneric`: Conical genericity used by the proof of Corollary 4.4, PDF p.11: interior of one LR chamber OR interior of the exterior of closed hive support. This is explicitly different from the affine SA genericity of PDF p.9.
--   - `JointCoordinates`: Joint variables: none is the dilation parameter t, some v a triple coordinate. PDF p.11, (35).
--   - `JointDegreeAtMost`: Joint polynomial degree bound: total degree in each triple block, and the separate t bound 3*choose(k-1,2), Corollary 4.4, PDF p.11.
--   - `exchangeLRBlocks`: Exchange lambda and mu, leaving nu fixed, Remark 5.1, PDF p.13.
-- source:
--   A polynomiality property for Littlewood-Richardson coefficients, arXiv:math/0308101v2, https://arxiv.org/abs/math/0308101v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07

/-!
Rassart, A polynomiality property for Littlewood--Richardson coefficients,
arXiv:math/0308101v2 (2003). All page citations below are PDF pages.
The coefficient is the homogeneous GL_k coefficient, never a determinant-shift
quotient. Frozen tableau and row-list diagram definitions are imported from the
pinned accepted library; all new objects are local to this paper. Compilation
is pending under the batch handoff.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P98

open QAlgorithms.Papers.Independent.Frontier30.P19

attribute [local instance] Classical.propDecidable

/-- Three blocks of padded coordinates, PDF pp.3,7. Blocks 0,1,2 are lambda,mu,nu. -/
abbrev Coordinates (k : ℕ) := Fin 3 × Fin k

/-- The coefficient in padded coordinates, PDF p.3. Only dominant triples
are used in statements. The frozen row-list diagram sorts the padded list;
on these antitone inputs it preserves the specified partition. There is no
determinant normalization. -/
def paddedLRCoefficient {k : ℕ} (x : Coordinates k → ℕ) : ℕ :=
  lrCoefficient k (QAlgorithms.Papers.Independent.Next46.P07.diagram (List.ofFn (fun i => x (0,i))))
    (QAlgorithms.Papers.Independent.Next46.P07.diagram (List.ofFn (fun i => x (1,i))))
    (QAlgorithms.Papers.Independent.Next46.P07.diagram (List.ofFn (fun i => x (2,i))))

example : skewCells ⊥ ⊥ = ∅ := by
  simp [skewCells]

example (k : ℕ) : lrCoefficient k ⊥ ⊥ ⊥ = 1 := by
  letI : IsEmpty (skewCells ⊥ ⊥) := ⟨fun a => by
    simpa [skewCells] using a.property⟩
  have hvalid : ∀ T : (skewCells ⊥ ⊥) → Fin k,
      IsLRFilling ⊥ ⊥ ⊥ T := by
    intro T
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact isEmptyElim a
    · intro i
      simp [YoungDiagram.rowLen_eq_card, YoungDiagram.row]
    · intro a
      exact isEmptyElim a
  simp only [lrCoefficient, if_pos (Finset.Subset.refl _)]
  rw [Finset.filter_true_of_mem (fun T _ => hvalid T)]
  simp

/-- The source's integral parameter domain, PDF pp.3,7--8; empty partitions allowed. -/
def IntegralDomain {k : ℕ} (x : Coordinates k → ℕ) : Prop :=
  (∀ b : Fin 3, Antitone (fun i => x (b,i))) ∧
  (∑ i, x (0,i)) + (∑ i, x (1,i)) = ∑ i, x (2,i) ∧
  (∀ i, x (0,i) ≤ x (2,i) ∧ x (1,i) ≤ x (2,i))

/-- The real size hyperplane, PDF pp.7--9. -/
def SizeEquation {k : ℕ} (x : Coordinates k → ℝ) : Prop :=
  (∑ i, x (0,i)) + (∑ i, x (1,i)) = ∑ i, x (2,i)

/-- The real cone Upsilon from (34), PDF p.11, with dominant nonnegative coordinates. -/
def RealDomain {k : ℕ} (x : Coordinates k → ℝ) : Prop :=
  SizeEquation x ∧ (∀ v, 0 ≤ x v) ∧
  (∀ b : Fin 3, Antitone (fun i => x (b,i))) ∧
  (∀ i, x (0,i) ≤ x (2,i) ∧ x (1,i) ≤ x (2,i))

/-- Real realization of an integral triple, PDF pp.7--8. -/
def realTriple {k : ℕ} (x : Coordinates k → ℕ) : Coordinates k → ℝ :=
  fun v => (x v : ℝ)

/-- Integral dilation, (21), PDF p.6. -/
def stretch {k : ℕ} (x : Coordinates k → ℕ) (N : ℕ) : Coordinates k → ℕ :=
  fun v => N * x v

example {k : ℕ} (x : Coordinates k → ℕ) : stretch x 1 = x := by
  funext v
  simp [stretch]

/-- Genuinely interior hive positions, the explicit range in (22), PDF p.6. -/
abbrev InteriorIndex (k : ℕ) :=
  {ij : Fin (k+1) × Fin (k+1) //
    0 < ij.1.val ∧ 0 < ij.2.val ∧ ij.1.val + ij.2.val < k}

/-- Rhombus origins; the guard i+j+2<=k handles k=1 without Nat truncation.
PDF p.6, (17)--(19). The product order fixes orientation before origin. -/
abbrev RhombusIndex (k : ℕ) :=
  Fin 3 × {ij : Fin (k+1) × Fin (k+1) // ij.1.val + ij.2.val + 2 ≤ k}

/-- Coefficients of a hive vertex after the boundary substitution (20), PDF p.6.
At corners use row zero first, then column zero, then the diagonal. The only
alternative values meet at (k,0), where they agree on the size hyperplane. -/
def vertexCoefficient (k i j : ℕ) (c : InteriorIndex k ⊕ Coordinates k) : ℤ :=
  if i = 0 then
    match c with
    | .inl _ => 0
    | .inr v => if v.1 = 0 ∧ v.2.val < j then 1 else 0
  else if j = 0 then
    match c with
    | .inl _ => 0
    | .inr v => if v.1 = 2 ∧ v.2.val < i then 1 else 0
  else if i + j = k then
    match c with
    | .inl _ => 0
    | .inr v => (if v.1 = 0 then 1 else 0) +
        (if v.1 = 1 ∧ v.2.val < i then 1 else 0)
  else
    match c with
    | .inl q => if q.val.1.val = i ∧ q.val.2.val = j then 1 else 0
    | .inr _ => 0

/-- Left minus right of HC, with the sign chosen for <=0; (17)--(22), PDF p.6. -/
def rhombusCoefficient {k : ℕ} (r : RhombusIndex k)
    (c : InteriorIndex k ⊕ Coordinates k) : ℤ :=
  let i := r.2.val.1.val
  let j := r.2.val.2.val
  let a := fun s t => vertexCoefficient k s t c
  if r.1 = 0 then a i j + a (i+1) (j+1) - a (i+1) j - a i (j+1)
  else if r.1 = 1 then a (i+2) j + a i (j+1) - a (i+1) j - a (i+1) (j+1)
  else a (i+1) j + a i (j+2) - a i (j+1) - a (i+1) (j+1)

/-- Actual matrix E_k=[b|I], (23)--(24), PDF p.7.
No equality to LR counts is a field of this construction. -/
def hiveMatrix (k : ℕ) :
    Matrix (RhombusIndex k) (InteriorIndex k ⊕ RhombusIndex k) ℤ :=
  fun r c => match c with
  | .inl q => rhombusCoefficient r (.inl q)
  | .inr s => if r = s then 1 else 0

/-- Actual boundary matrix B_k, the negative boundary coefficients of HC,
(22)--(24), PDF pp.6--7. -/
def boundaryMatrix (k : ℕ) : Matrix (RhombusIndex k) (Coordinates k) ℤ :=
  fun r v => -rhombusCoefficient r (.inr v)

/-- Boundary right-hand side B_k x, PDF p.7, (25). -/
def boundaryRhs {k : ℕ} (x : Coordinates k → ℕ) : RhombusIndex k → ℤ :=
  fun r => ∑ v, boundaryMatrix k r v * (x v : ℤ)

/-- Nonnegative real kernel condition in Definition 1.4, PDF p.4. -/
def PointedKernel {R C : Type*} [Fintype C] (M : Matrix R C ℤ) : Prop :=
  ∀ a : C → ℝ, (∀ j, 0 ≤ a j) →
    (∀ i, ∑ j, (M i j : ℝ) * a j = 0) → a = 0

/-- Actual nonnegative integral fiber, Definition 1.4, PDF p.4. -/
def partitionFiber {R C : Type*} [Fintype C] (M : Matrix R C ℤ) (b : R → ℤ) :=
  {a : C → ℕ // ∀ i, ∑ j, M i j * (a j : ℤ) = b i}

/-- Vector partition count, Definition 1.4, PDF p.4.
Nat.card is used only with pointed kernels in theorem statements. The kernel
condition is a conclusion for E_k, not an assumed matrix property. -/
def vectorPartition {R C : Type*} [Fintype C] (M : Matrix R C ℤ) (b : R → ℤ) : ℕ :=
  Nat.card (partitionFiber M b)

example {k : ℕ} (r : RhombusIndex k) : hiveMatrix k r (.inr r) = 1 := by
  simp [hiveMatrix]

example {k : ℕ} (v : Coordinates k) : vertexCoefficient k 0 0 (.inr v) = 0 := by
  simp [vertexCoefficient]

/-- The first k=3 square inequality is a_11 <= lambda_1+nu_1,
(17),(20), PDF p.6. These entries pin both the interior and boundary signs. -/
example : hiveMatrix 3 (0, ⟨(0,0), by decide⟩)
    (.inl ⟨(1,1), by decide⟩) = 1 := by
  norm_num [hiveMatrix, rhombusCoefficient, vertexCoefficient, Fin.ext_iff]

example : boundaryMatrix 3 (0, ⟨(0,0), by decide⟩) (0,0) = 1 := by
  norm_num [boundaryMatrix, rhombusCoefficient, vertexCoefficient, Fin.ext_iff]

example : boundaryMatrix 3 (0, ⟨(0,0), by decide⟩) (2,0) = 1 := by
  norm_num [boundaryMatrix, rhombusCoefficient, vertexCoefficient, Fin.ext_iff]

/-- Positive hull of a specified column set, including zero, PDF pp.4--5. -/
def columnCone {R C : Type*} [Fintype C] (M : Matrix R C ℤ) (S : Finset C) :
    Set (R → ℝ) :=
  {b | ∃ a : C → ℝ, (∀ j, 0 ≤ a j) ∧ (∀ j, j ∉ S → a j = 0) ∧
    ∀ i, b i = ∑ j, (M i j : ℝ) * a j}

/-- Column bases, PDF p.5. Cardinality and independence specify full row rank.
The empty basis is allowed for the zero-row matrix (k=1). -/
def columnBases {R C : Type*} [Fintype R] [Fintype C] (M : Matrix R C ℤ) :
    Set (Finset C) :=
  {S | S.card = Fintype.card R ∧
    LinearIndependent ℝ (fun j : S => fun i : R => (M i j.val : ℝ))}

/-- Cell at b: intersection of all basis cones containing b, PDF p.5.
Taking these intersections and their faces is the common refinement, not an
arbitrarily chosen polynomiality subdivision. -/
def chamberAt {R C : Type*} [Fintype R] [Fintype C]
    (M : Matrix R C ℤ) (b : R → ℝ) : Set (R → ℝ) :=
  {y | ∀ S ∈ columnBases M, b ∈ columnCone M S → y ∈ columnCone M S}

/-- Exposed faces of a polyhedral cone, including the cone itself (ell=0).
Used to retain all lattice boundary points, PDF pp.4--5. -/
def faces {V : Type*} [AddCommGroup V] [Module ℝ V] (C : Set V) : Set (Set V) :=
  {F | ∃ ell : V →ₗ[ℝ] ℝ,
    (∀ y ∈ C, 0 ≤ ell y) ∧ F = {y | y ∈ C ∧ ell y = 0}}

/-- The actual vector-partition chamber complex, common refinement of basis
cones with all their faces, PDF p.5. Inputs outside column support create no cell. -/
def partitionComplex {R C : Type*} [Fintype R] [Fintype C]
    (M : Matrix R C ℤ) : Set (Set (R → ℝ)) :=
  {F | ∃ b ∈ columnCone M Finset.univ, F ∈ faces (chamberAt M b)}

/-- The LR complex of Definition 2.4, PDF pp.7--8. Pull back the actual
E_k complex along B_k, then intersect with C_k^(1) and C_k^(2), retaining faces. -/
def lrComplex (k : ℕ) : Set (Set (Coordinates k → ℝ)) :=
  {F | ∃ C ∈ partitionComplex (hiveMatrix k),
    F ∈ faces {x | RealDomain x ∧
      (fun r => ∑ v, (boundaryMatrix k r v : ℝ) * x v) ∈ C}}

/-- Closed hive support, as the union of the constructed LR cones, PDF pp.7--8. -/
def lrSupport (k : ℕ) : Set (Coordinates k → ℝ) :=
  {x | ∃ C ∈ lrComplex k, x ∈ C}

/-- Total degree inside EACH of the three coordinate blocks, PDF p.10,
Theorem 4.1; not the maximum of individual-variable degrees. -/
def BlockDegreeAtMost {k : ℕ} (p : MvPolynomial (Coordinates k) ℚ) (D : ℕ) : Prop :=
  ∀ m ∈ p.support, ∀ b : Fin 3, (∑ i : Fin k, m (b,i)) ≤ D

/-- Evaluation of a rational polynomial on real coordinates, PDF pp.9--11. -/
def evalReal {I : Type*} (p : MvPolynomial I ℚ) (x : I → ℝ) : ℝ :=
  MvPolynomial.eval₂ (algebraMap ℚ ℝ) x p

/-- Positive common period and residue-class polynomials on the integral
size hyperplane, Corollary 2.5, PDF p.8. Total degree uses the printed coarse bound. -/
def QuasipolynomialOn {k : ℕ} (C : Set (Coordinates k → ℝ)) (D : ℕ) : Prop :=
  ∃ period : ℕ, 0 < period ∧
    ∃ pieces : (Coordinates k → ZMod period) → MvPolynomial (Coordinates k) ℚ,
      (∀ r, (pieces r).totalDegree ≤ D) ∧
      ∀ x : Coordinates k → ℕ, IntegralDomain x → realTriple x ∈ C →
        MvPolynomial.eval (fun v => (x v : ℚ)) (pieces (fun v => (x v : ZMod period))) = (paddedLRCoefficient x : ℚ)

example {k : ℕ} (D : ℕ) : BlockDegreeAtMost (0 : MvPolynomial (Coordinates k) ℚ) D := by
  simp [BlockDegreeAtMost]

/-- Positive roots e_i-e_j, PDF p.2, with zero-based i<j. -/
abbrev PositiveRoot (k : ℕ) := {ij : Fin k × Fin k // ij.1 < ij.2}

/-- Kostant's K, Definition 1.2, PDF p.3: a genuine count of root decompositions.
This is finite: dotting with (k-1,k-2,...,0) bounds each nonnegative multiplicity. -/
def kostant {k : ℕ} (v : Fin k → ℝ) : ℕ :=
  Nat.card {a : PositiveRoot k → ℕ // ∀ i : Fin k,
    (∑ r : PositiveRoot k,
      (a r : ℝ) * ((if i = r.val.1 then 1 else 0) -
        (if i = r.val.2 then 1 else 0))) = v i}

/-- Half sum of positive roots, PDF p.3. Arithmetic is in R before subtracting. -/
def rootHalfSum (k : ℕ) : Fin k → ℝ :=
  fun i => ((k : ℝ) - 1 - 2 * (i.val : ℝ)) / 2

/-- sigma(e_i)=e_{sigma(i)}; coordinates therefore use sigma inverse, PDF p.3. -/
def permuteRootCoordinates {k : ℕ} (sigma : Equiv.Perm (Fin k)) (v : Fin k → ℝ) : Fin k → ℝ :=
  fun i => v (sigma.symm i)

/-- Steinberg argument from (14), PDF p.4. -/
def steinbergArgument {k : ℕ} (x : Coordinates k → ℝ)
    (sigma tau : Equiv.Perm (Fin k)) : Fin k → ℝ :=
  fun i => permuteRootCoordinates sigma (fun j => x (0,j) + rootHalfSum k j) i +
    permuteRootCoordinates tau (fun j => x (1,j) + rootHalfSum k j) i - (x (2,i) + 2 * rootHalfSum k i)

/-- Number of inversions in the usual order 0<...<k-1, PDF pp.3--4. -/
def inversions {k : ℕ} (sigma : Equiv.Perm (Fin k)) : ℕ :=
  (Finset.univ.filter fun ij : Fin k × Fin k =>
    ij.1 < ij.2 ∧ sigma ij.2 < sigma ij.1).card

/-- Actual alternating Kostant sum, (14), PDF p.4, with integer signs. -/
def steinbergSum {k : ℕ} (x : Coordinates k → ℝ) : ℤ :=
  ∑ sigma : Equiv.Perm (Fin k), ∑ tau : Equiv.Perm (Fin k),
    (-1 : ℤ) ^ inversions (sigma * tau) * (kostant (steinbergArgument x sigma tau) : ℤ)

example (k : ℕ) : permuteRootCoordinates (1 : Equiv.Perm (Fin k)) (rootHalfSum k) = rootHalfSum k := by
  rfl

example : rootHalfSum 3 0 = 1 ∧ rootHalfSum 3 1 = 0 ∧ rootHalfSum 3 2 = -1 := by
  norm_num [rootHalfSum]

/-- Positive roots written in simple-root coordinates, PDF p.5. -/
def rootMatrix (k : ℕ) : Matrix (Fin (k-1)) (PositiveRoot k) ℤ :=
  fun i r => if r.val.1.val ≤ i.val ∧ i.val < r.val.2.val then 1 else 0

/-- Coordinates in the simple-root basis on sum v_i=0, PDF pp.2,5. -/
def simpleCoordinates {k : ℕ} (v : Fin k → ℝ) : Fin (k-1) → ℝ :=
  fun i => ∑ j : Fin k, if j.val ≤ i.val then v j else 0

/-- Kostant chamber complex in the standard sum-zero realization, PDF pp.5,8. -/
def kostantComplex (k : ℕ) : Set (Set (Fin k → ℝ)) :=
  {C | ∃ B ∈ partitionComplex (rootMatrix k),
    C = {v | (∑ i, v i) = 0 ∧ simpleCoordinates v ∈ B}}

/-- Interior relative to the root hyperplane, PDF pp.8--9. -/
def rootInterior {k : ℕ} (C : Set (Fin k → ℝ)) : Set (Fin k → ℝ) :=
  {v | ∃ h : (∑ i, v i) = 0,
    (⟨v,h⟩ : {w : Fin k → ℝ // (∑ i, w i) = 0}) ∈
      interior {w : {w : Fin k → ℝ // (∑ i, w i) = 0} | w.val ∈ C}}

/-- Associated Kostant polynomial as in Definition 3.2, PDF p.9. This chooses
only a Kostant piece from the standard piecewise-polynomial background (p.5),
never a polynomial specified by LR values. The explicit zero fallback makes the
construction total even on sets that are not Kostant chambers. Polynomials may
differ off the root hyperplane, where they are never evaluated by the theorem. -/
def kostantPiece {k : ℕ} (C : Set (Fin k → ℝ)) : MvPolynomial (Fin k) ℚ :=
  if h : ∃ p : MvPolynomial (Fin k) ℚ,
      p.totalDegree ≤ Nat.choose (k-1) 2 ∧
      ∀ z : Fin k → ℤ, (∑ i, z i) = 0 →
        (fun i => (z i : ℝ)) ∈ C →
        evalReal p (fun i => (z i : ℝ)) = (kostant (fun i => (z i : ℝ)) : ℝ) then
    Classical.choose h
  else 0

/-- Fixed chamber labels are the chamber sets themselves; `none` is label 0
outside support. Choosing among interiors is independent of LR coefficients.
This avoids any dependence on an incidental integer numbering, PDF p.9. -/
def kostantLabel {k : ℕ} (v : Fin k → ℝ) : Option (Set (Fin k → ℝ)) :=
  if h : ∃ C ∈ kostantComplex k, v ∈ rootInterior C then
    some (Classical.choose h)
  else none

/-- A fixed total order on permutations, chosen once by a finite enumeration,
Definition 3.2, PDF p.9. The sum itself is invariant under that enumeration. -/
def permutationOrder (k : ℕ) : LinearOrder (Equiv.Perm (Fin k)) :=
  LinearOrder.lift' (Fintype.equivFin (Equiv.Perm (Fin k)))
    (Fintype.equivFin (Equiv.Perm (Fin k))).injective

/-- The type matrix indexed by the fixed finite permutation index set;
Definition 3.2, PDF p.9. Reindexing a matrix by a total order changes no entries. -/
def steinbergType {k : ℕ} (x : Coordinates k → ℝ) :=
  letI : LinearOrder (Equiv.Perm (Fin k)) := permutationOrder k
  fun sigma tau : Equiv.Perm (Fin k) => kostantLabel (steinbergArgument x sigma tau)

/-- P is computed by the alternating sum of associated Kostant pieces, (28),
PDF p.9. No equality to LR coefficients is assumed in any definition. -/
def steinbergP {k : ℕ} (x : Coordinates k → ℝ) : ℝ :=
  ∑ sigma : Equiv.Perm (Fin k), ∑ tau : Equiv.Perm (Fin k),
    (-1 : ℝ) ^ inversions (sigma * tau) *
      match steinbergType x sigma tau with
      | none => 0
      | some C => evalReal (kostantPiece C) (steinbergArgument x sigma tau)

/-- Fundamental weight omega_(j+1), (6), PDF p.2.
The index is Fin(k-1), correcting the nonexistent omega_k in (27), PDF p.9. -/
def fundamentalWeight (k : ℕ) (j : Fin (k-1)) : Fin k → ℝ :=
  fun i => if i.val < j.val + 1 then
    ((k : ℝ) - ((j.val + 1 : ℕ) : ℝ)) / (k : ℝ) else -((j.val + 1 : ℕ) : ℝ) / (k : ℝ)

/-- Indices of all affine Steinberg walls, (27), PDF p.9. -/
abbrev WallIndex (k : ℕ) :=
  Equiv.Perm (Fin k) × Equiv.Perm (Fin k) × Equiv.Perm (Fin k) × Fin (k-1)

/-- Affine wall equation INCLUDING the delta shifts, (27)--(31), PDF pp.9--10. -/
def wallValue {k : ℕ} (w : WallIndex k) (x : Coordinates k → ℝ) : ℝ :=
  ∑ i, steinbergArgument x w.1 w.2.1 i *
    permuteRootCoordinates w.2.2.1 (fundamentalWeight k w.2.2.2) i

/-- Open regions of the affine Steinberg arrangement in the size hyperplane,
PDF p.9. All sign patterns are included; empty patterns are harmless. -/
def steinbergRegion {k : ℕ} (s : WallIndex k → Bool) : Set (Coordinates k → ℝ) :=
  {x | SizeEquation x ∧ ∀ w, if s w then 0 < wallValue w x else wallValue w x < 0}

/-- Size-hyperplane relative interior, PDF pp.10--11. -/
def sizeInterior {k : ℕ} (C : Set (Coordinates k → ℝ)) : Set (Coordinates k → ℝ) :=
  {x | ∃ h : SizeEquation x,
    (⟨x,h⟩ : {y : Coordinates k → ℝ // SizeEquation y}) ∈
      interior {y : {y : Coordinates k → ℝ // SizeEquation y} | y.val ∈ C}}

/-- Conical genericity used by the proof of Corollary 4.4, PDF p.11:
interior of one LR chamber OR interior of the exterior of closed hive support.
This is explicitly different from the affine SA genericity of PDF p.9. -/
def LRGeneric {k : ℕ} (x : Coordinates k → ℝ) : Prop :=
  (∃ C ∈ lrComplex k, x ∈ sizeInterior C) ∨
    x ∈ sizeInterior (lrSupport k)ᶜ

/-- Joint variables: none is the dilation parameter t, some v a triple coordinate.
PDF p.11, (35). -/
abbrev JointCoordinates (k : ℕ) := Option (Coordinates k)

/-- Joint polynomial degree bound: total degree in each triple block, and the
separate t bound 3*choose(k-1,2), Corollary 4.4, PDF p.11. -/
def JointDegreeAtMost {k : ℕ} (p : MvPolynomial (JointCoordinates k) ℚ) (D : ℕ) : Prop :=
  ∀ m ∈ p.support,
    m none ≤ 3 * D ∧ ∀ b : Fin 3, (∑ i : Fin k, m (some (b,i))) ≤ D

/-- Exchange lambda and mu, leaving nu fixed, Remark 5.1, PDF p.13. -/
def exchangeLRBlocks {k : ℕ} {A : Type*} (x : Coordinates k → A) : Coordinates k → A :=
  fun v => if v.1 = 0 then x (1,v.2) else if v.1 = 1 then x (0,v.2) else x v

example {k : ℕ} (x : Coordinates k → ℕ) (i : Fin k) :
    exchangeLRBlocks x (0,i) = x (1,i) := by
  simp [exchangeLRBlocks]

example {k : ℕ} (D : ℕ) :
    JointDegreeAtMost (0 : MvPolynomial (JointCoordinates k) ℚ) D := by
  simp [JointDegreeAtMost]

end QAlgorithms.Papers.Independent.Intake100.P98


