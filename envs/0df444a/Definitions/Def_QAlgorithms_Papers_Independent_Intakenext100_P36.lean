-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P36
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P36
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T05:11:07.344995+00:00
-- url     : https://prove2.me/theorems/696fea55-be5f-413e-a3a1-00d73e82fee2
-- title:
--   Definitions for Computing Stabilized Norms for Quantum Operations via the Theory of Completely Bounded Maps
-- statement:
--   The objects the formalized statements of *Computing Stabilized Norms for Quantum Operations via the Theory of Completely Bounded Maps* (arXiv:0711.3636) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `extendedInducedNorm`: PDF p.2: the accepted induced Schatten norm at p=infinity, embedded in ENNReal. The real supremum is meaningful: the matrix domain is finite dimensional and phi is complex-linear. No new norm convention is introduced.
--   - `extendedCBNorm`: PDF p.3, Definition 2: the accepted CB Schatten norm at p=infinity, embedded in ENNReal. The source's finite-matrix stabilization guarantees boundedness of the real supremum for every such phi. The accepted m=0 term adds only zero. The arbitrary-operator-space norm below instead uses a complete supremum.
--   - `rectangularDiamondNorm`: PDF p.2, Definition 1: the induced trace norm with input-dimension ancilla; trace is unnormalized, and no factor 1/2 is used.
--   - `operatorSpaceBlockNorm`: PDF p.4: inherited C*-matrix norm, with the canonical C*-positive order. No concrete Hilbert realization, closedness, or unit is required of a subspace.
--   - `operatorSpaceAmplification`: PDF p.4: entrywise amplification into the ambient C*-algebra, whose inherited matrix norms restrict to the possibly nonclosed operator subspace M.
--   - `operatorSpaceInducedNorm`: PDF pp.2,4: ordinary induced norm into the operator subspace.
--   - `operatorSpaceCBNorm`: PDF p.4, Definition 5: all finite entrywise amplifications with the inherited C*-matrix norm. Extended values do not presuppose complete boundedness.
--   - `IsGeneralizedChoiKraus`: PDF p.8: arbitrary finite generalized Choi–Kraus representation, including empty families for the zero map; no Kraus normalization is imposed.
--   - `factorizationCost`: PDF p.8: row/column factorization cost, with the source's asymmetric stars.
--   - `representationCosts`: PDF p.8, Corollary 20: costs of all actual finite representations of phi.
--   - `firstReducedLeft`: PDF p.10, Step 2: D_j is computed from the supplied coefficients.
--   - `BasisReduction`: PDF p.10, Steps 1–3: only basis choices and their coordinates are fields. Independence of the final right family and the norm formula are theorem content.
--   - `reducedRight`: PDF p.10, Step 3: the final right family is computed from the second coordinates.
--   - `changedLeft`: PDF p.10, Step 4: G_j=sum_i (S^-1)_(i,j) E_i.
--   - `changedRight`: PDF p.10, Step 4: H_i=sum_j S_(i,j) F_j; no transpose or conjugation.
--   - `changeCost`: PDF pp.10,17: the objective; all uses below restrict S to actual invertibles.
--   - `unitaryDifference`: PDF p.13: the constructed map X -> U X U-adjoint - X on all matrices.
--   - `IsSmallestSpectralDisk`: PDF p.13: a smallest enclosing disk, not the diameter of the spectral set.
--   - `exampleUnitary`: Example 27, PDF p.19: the actual diagonal matrix, in the printed order.
-- source:
--   Computing Stabilized Norms for Quantum Operations via the Theory of Completely Bounded Maps, arXiv:0711.3636v1, https://arxiv.org/abs/0711.3636v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_ChannelDiamondNorm
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P49

/-! Johnston–Kribs–Paulsen, arXiv:0711.3636v1. All page citations are PDF pages.
Norm comparisons and infima take values in ENNReal. Finite matrix norms reuse
the accepted real-valued norms; arbitrary-operator-space suprema retain infinity
until finite bounds are asserted. Matrix norms are the frozen Euclidean operator norm
and unnormalized trace norm. Pinned accepted-library imports supply matrix/map types and the bilinear trace dual.
The extended and rectangular norm adapters below have different interfaces from
the accepted real-valued and endomorphism-only norms. Only the eight selected paper results are targets;
cited background and ambiguous runtime claims are recorded in HARD.md. -/

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P36

-- Reuse the pinned full-matrix and complex-linear map types without redeclaring them.
local notation "Mat" => QAlgorithms.Papers.Independent.Information100.P50.M
local notation "Map" => QAlgorithms.Papers.Independent.Information100.P50.Lin

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

/-- PDF p.2: the accepted induced Schatten norm at p=infinity, embedded in ENNReal.
The real supremum is meaningful: the matrix domain is finite dimensional and phi
is complex-linear. No new norm convention is introduced. -/
def extendedInducedNorm {n k : ℕ} (phi : Map n k) : ℝ≥0∞ :=
  ENNReal.ofReal (QAlgorithms.Papers.Independent.Information100.P50.inducedNorm ⊤ phi)

/-- PDF p.3, Definition 2: the accepted CB Schatten norm at p=infinity,
embedded in ENNReal. The source's finite-matrix stabilization guarantees boundedness
of the real supremum for every such phi. The accepted m=0 term adds only zero.
The arbitrary-operator-space norm below instead uses a complete supremum. -/
def extendedCBNorm {n k : ℕ} (phi : Map n k) : ℝ≥0∞ :=
  ENNReal.ofReal (QAlgorithms.Papers.Independent.Information100.P50.cbNorm ⊤ phi)

/-- PDF p.2, Definition 1: the induced trace norm with input-dimension ancilla;
trace is unnormalized, and no factor 1/2 is used. -/
def rectangularDiamondNorm {n k : ℕ} (phi : Map n k) : ℝ≥0∞ :=
  ⨆ X : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ,
    ⨆ (_ : traceNorm X ≤ 1),
      ENNReal.ofReal (traceNorm (idTensorSuperop (R := Fin n) phi X))

/-- PDF p.4: inherited C*-matrix norm, with the canonical C*-positive order.
No concrete Hilbert realization, closedness, or unit is required of a subspace. -/
def operatorSpaceBlockNorm {A : Type*} [NonUnitalCStarAlgebra A] {m : ℕ}
    (Y : Matrix (Fin m) (Fin m) A) : ℝ := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact ‖CStarMatrix.ofMatrix Y‖

/-- PDF p.4: entrywise amplification into the ambient C*-algebra, whose inherited
matrix norms restrict to the possibly nonclosed operator subspace M. -/
def operatorSpaceAmplification {A : Type*} [NonUnitalCStarAlgebra A]
    {n m : ℕ} {M : Submodule ℂ A} (phi : Mat n →ₗ[ℂ] M)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : Matrix (Fin m) (Fin m) A :=
  fun i j => (phi (fun a b => X (i, a) (j, b)) : A)

/-- PDF pp.2,4: ordinary induced norm into the operator subspace. -/
def operatorSpaceInducedNorm {A : Type*} [NonUnitalCStarAlgebra A]
    {n : ℕ} {M : Submodule ℂ A} (phi : Mat n →ₗ[ℂ] M) : ℝ≥0∞ :=
  ⨆ X : Mat n, ⨆ (_ : specNorm X ≤ 1), ENNReal.ofReal ‖(phi X : A)‖

/-- PDF p.4, Definition 5: all finite entrywise amplifications with the inherited
C*-matrix norm. Extended values do not presuppose complete boundedness. -/
def operatorSpaceCBNorm {A : Type*} [NonUnitalCStarAlgebra A]
    {n : ℕ} {M : Submodule ℂ A} (phi : Mat n →ₗ[ℂ] M) : ℝ≥0∞ :=
  ⨆ m : ℕ, ⨆ (_ : 0 < m),
    ⨆ X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      ⨆ (_ : specNorm X ≤ 1),
        ENNReal.ofReal (operatorSpaceBlockNorm (operatorSpaceAmplification phi X))

/-- PDF p.8: arbitrary finite generalized Choi–Kraus representation, including
empty families for the zero map; no Kraus normalization is imposed. -/
def IsGeneralizedChoiKraus {n k m : ℕ} (phi : Map n k)
    (A : Fin m → Matrix (Fin k) (Fin n) ℂ)
    (B : Fin m → Matrix (Fin n) (Fin k) ℂ) : Prop :=
  ∀ X, phi X = ∑ i, A i * X * B i

/-- PDF p.8: row/column factorization cost, with the source's asymmetric stars. -/
def factorizationCost {n k m : ℕ}
    (A : Fin m → Matrix (Fin k) (Fin n) ℂ)
    (B : Fin m → Matrix (Fin n) (Fin k) ℂ) : ℝ :=
  Real.sqrt (specNorm (∑ i, A i * (A i)ᴴ)) *
    Real.sqrt (specNorm (∑ i, (B i)ᴴ * B i))

/-- PDF p.8, Corollary 20: costs of all actual finite representations of phi. -/
def representationCosts {n k : ℕ} (phi : Map n k) : Set ℝ≥0∞ :=
  {r | ∃ m : ℕ, ∃ A : Fin m → Matrix (Fin k) (Fin n) ℂ,
    ∃ B : Fin m → Matrix (Fin n) (Fin k) ℂ,
      IsGeneralizedChoiKraus phi A B ∧ r = ENNReal.ofReal (factorizationCost A B)}

/-- PDF p.10, Step 2: D_j is computed from the supplied coefficients. -/
def firstReducedLeft {n k m l : ℕ}
    (A : Fin m → Matrix (Fin k) (Fin n) ℂ) (d : Fin m → Fin l → ℂ)
    (j : Fin l) : Matrix (Fin k) (Fin n) ℂ := ∑ i, d i j • A i

/-- PDF p.10, Steps 1–3: only basis choices and their coordinates are fields.
Independence of the final right family and the norm formula are theorem content. -/
structure BasisReduction {n k m : ℕ}
    (A : Fin m → Matrix (Fin k) (Fin n) ℂ)
    (B : Fin m → Matrix (Fin n) (Fin k) ℂ) where
  l : ℕ
  C : Fin l → Matrix (Fin n) (Fin k) ℂ
  C_independent : LinearIndependent ℂ C
  C_span : Submodule.span ℂ (Set.range C) = Submodule.span ℂ (Set.range B)
  d : Fin m → Fin l → ℂ
  B_coordinates : ∀ i, B i = ∑ j, d i j • C j
  p : ℕ
  E : Fin p → Matrix (Fin k) (Fin n) ℂ
  E_independent : LinearIndependent ℂ E
  E_span : Submodule.span ℂ (Set.range E) =
    Submodule.span ℂ (Set.range (firstReducedLeft A d))
  c : Fin l → Fin p → ℂ
  D_coordinates : ∀ j, firstReducedLeft A d j = ∑ i, c j i • E i

/-- PDF p.10, Step 3: the final right family is computed from the second coordinates. -/
def reducedRight {n k m : ℕ}
    {A : Fin m → Matrix (Fin k) (Fin n) ℂ}
    {B : Fin m → Matrix (Fin n) (Fin k) ℂ} (r : BasisReduction A B)
    (i : Fin r.p) : Matrix (Fin n) (Fin k) ℂ := ∑ j, r.c j i • r.C j

/-- PDF p.10, Step 4: G_j=sum_i (S^-1)_(i,j) E_i. -/
def changedLeft {n k p : ℕ} (E : Fin p → Matrix (Fin k) (Fin n) ℂ)
    (S : Mat p) (j : Fin p) : Matrix (Fin k) (Fin n) ℂ :=
  ∑ i, (S⁻¹) i j • E i

/-- PDF p.10, Step 4: H_i=sum_j S_(i,j) F_j; no transpose or conjugation. -/
def changedRight {n k p : ℕ} (F : Fin p → Matrix (Fin n) (Fin k) ℂ)
    (S : Mat p) (i : Fin p) : Matrix (Fin n) (Fin k) ℂ := ∑ j, S i j • F j

/-- PDF pp.10,17: the objective; all uses below restrict S to actual invertibles. -/
def changeCost {n k p : ℕ} (E : Fin p → Matrix (Fin k) (Fin n) ℂ)
    (F : Fin p → Matrix (Fin n) (Fin k) ℂ) (S : Mat p) : ℝ :=
  factorizationCost (changedLeft E S) (changedRight F S)

/-- PDF p.13: the constructed map X -> U X U-adjoint - X on all matrices. -/
def unitaryDifference {n : ℕ} (U : Mat n) : Map n n where
  toFun X := conjSuperop U X - X
  map_add' X Y := by
    simp only [conjSuperop, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c X := by
    simp [conjSuperop, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-- PDF p.13: a smallest enclosing disk, not the diameter of the spectral set. -/
def IsSmallestSpectralDisk {n : ℕ} (U : Mat n) (center : ℂ) (radius : ℝ) : Prop :=
  0 ≤ radius ∧ (∀ z ∈ spectrum ℂ U, dist z center ≤ radius) ∧
    ∀ (c : ℂ) (r : ℝ), 0 ≤ r → (∀ z ∈ spectrum ℂ U, dist z c ≤ r) → radius ≤ r

/-- Example 27, PDF p.19: the actual diagonal matrix, in the printed order. -/
def exampleUnitary : Mat 3 :=
  Matrix.diagonal ![Complex.exp (((5 * Real.pi / 4 : ℝ) : ℂ) * Complex.I),
    Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I),
    Complex.exp (((3 * Real.pi / 4 : ℝ) : ℂ) * Complex.I)]

/-- Sanity: empty sums supply the zero representation, including zero dimensions. -/
example {n k : ℕ} (A : Fin 0 → Matrix (Fin k) (Fin n) ℂ)
    (B : Fin 0 → Matrix (Fin n) (Fin k) ℂ) : IsGeneralizedChoiKraus (0 : Map n k) A B := by
  intro X
  simp

/-- Sanity: the empty objective is exactly zero. -/
example {n k : ℕ} (A : Fin 0 → Matrix (Fin k) (Fin n) ℂ)
    (B : Fin 0 → Matrix (Fin n) (Fin k) ℂ) : factorizationCost A B = 0 := by
  letI : NormedAddCommGroup (Matrix (Fin k) (Fin k) ℂ) :=
    Matrix.instL2OpNormedAddCommGroup
  simp [factorizationCost, specNorm]

/-- Sanity: entrywise amplification of zero is zero in the actual ambient algebra. -/
example {A : Type*} [NonUnitalCStarAlgebra A] {n m : ℕ} (M : Submodule ℂ A)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    operatorSpaceAmplification (0 : Mat n →ₗ[ℂ] M) X = 0 := by
  ext i j
  change (((0 : Mat n →ₗ[ℂ] M) (fun a b => X (i, a) (j, b))) : A) = 0
  exact congrArg (fun z : M => (z : A)) (LinearMap.zero_apply _)

/-- Sanity: the constructed unitary difference vanishes on the identity unitary. -/
example {n : ℕ} (X : Mat n) : unitaryDifference (1 : Mat n) X = 0 := by
  simp [unitaryDifference, conjSuperop]

/-- Sanity: the bilinear trace dual of zero is zero, without any hidden conjugation. -/
example {n k : ℕ} : traceDual (0 : Map n k) = 0 := by
  ext X i j
  change (∑ a : Fin k, ∑ b : Fin k, (0 : ℂ) * X a b) = 0
  simp

end QAlgorithms.Papers.Independent.Intakenext100.P36


