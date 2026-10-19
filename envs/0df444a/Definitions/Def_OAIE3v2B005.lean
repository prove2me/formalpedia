-- Prove2me | Definitions.Def_OAIE3v2B005
-- name    : OAIE3v2B005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:57:10.349035+00:00
-- url     : https://prove2.me/theorems/000002ff-eb1f-4cf3-9a98-9a5bef65e7f8
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 6 of 311
-- statement:
--   Definitions bundle 6 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Estimates/BSGIndicator.lean`, `Estimates/MinkowskiSecondInduction.lean`, `Estimates/PrimitiveExtension.lean`, `Estimates/RealDirectionExtension.lean`, `Estimates/RealSubquotientEquiv.lean`, `Estimates/RealificationModuleTopology.lean`, `FixedDensity/OrderedRemoval.lean`, `Geometry/BoxCertificate.lean`, `Geometry/MinkowskiSecondBox.lean`, `Geometry/MinkowskiSecondBoxGlue.lean`, `Geometry/NativeTernaryCoordinate.lean`, `Linear/CommonKernelRangeEquiv.lean`, `Linear/MatrixSupInverse.lean`, `Linear/ShortGeneratingBasisBound.lean`, `Nilpotent/NiltestVerticalBounds.lean`, `Polynomial/PolynomialDeterminantDerivativeBound.lean`, `Probability/BSGDensity.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BSGIndicator
namespace OAI

section

section BSGIndicatorNotation

scoped[Indicator] notation3 "𝟭_[" s ", " R "]" => Set.indicator s fun _ ↦ (1 : R)

open scoped Indicator

scoped[Indicator] notation3 "𝟭_[" s "]" => 𝟭_[s, _]

end BSGIndicatorNotation

section BSGIndicatorAlgebra

open scoped Indicator

variable {F α β M₀ N₀ : Type*}

namespace Set
open scoped _root_.Set
variable [MonoidWithZero M₀] [MonoidWithZero N₀] {s : Set α}

variable (M₀) in
@[simp] lemma indicator_one_image (e : α ≃ β) (s : Set α) (b : β) :
    𝟭_[e '' s, M₀] b = 𝟭_[s] (e.symm b) := by classical simp [_root_.Set.indicator_apply]

variable [Nontrivial M₀] {a : α}

@[simp high] lemma indicator_one_apply_eq_zero : 𝟭_[s, M₀] a = 0 ↔ a ∉ s := by
  classical exact one_ne_zero.ite_eq_right_iff

@[simp high] lemma indicator_one_eq_zero : 𝟭_[s, M₀] = 0 ↔ s = ∅ := by
  simp [funext_iff, _root_.Set.eq_empty_iff_forall_notMem]

end Set

end BSGIndicatorAlgebra

section BSGIndicatorOrder

open scoped Indicator

namespace Set
open scoped _root_.Set
variable {α M : Type*} [Zero M] [One M]

section Preorder
variable [Preorder M] [ZeroLEOneClass M] {s : Set α}

@[simp] lemma indicator_one_nonneg : 0 ≤ s.indicator (fun _ ↦ (1 : M)) :=
  _root_.Set.indicator_nonneg (by simp)

@[simp] lemma indicator_one_apply_nonneg {a : α} :
    0 ≤ s.indicator (fun _ ↦ (1 : M)) a := indicator_one_nonneg a

end Preorder

section PartialOrder
variable [PartialOrder M] [ZeroLEOneClass M] [NeZero (1 : M)] {s : Set α}

@[simp]
lemma indicator_one_pos [Nontrivial M] : 0 < s.indicator (fun _ ↦ (1 : M)) ↔ s.Nonempty := by
  classical
  simp [_root_.Set.indicator_apply, lt_iff_le_not_ge, Pi.le_def, apply_ite, ite_apply, Set.Nonempty,
    zero_lt_one.not_ge]

end PartialOrder
end Set

end BSGIndicatorOrder

section BSGIndicatorStar

open scoped ComplexConjugate Indicator

namespace Set
open scoped _root_.Set
variable {α R : Type*} [CommSemiring R] [StarRing R]

@[simp] lemma conj_indicator_one_apply (s : Set α) (a : α) : conj (𝟭_[s, R] a) = 𝟭_[s] a := by
  classical simp [_root_.Set.indicator_apply]

@[simp] lemma conj_indicator_one (s : Set α) : conj 𝟭_[s, R] = 𝟭_[s] := by ext; simp

end Set

end BSGIndicatorStar

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrimitiveExtension
namespace OAI


namespace Erdos3.BohrLattice.Primitive

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def IsPrimitive (z : ι → ℤ) : Prop :=
  ∃ u : ι → ℤ, ∑ i, u i * z i = 1

end Erdos3.BohrLattice.Primitive


namespace Erdos3.BohrLattice.PrimitiveExtension

open scoped BigOperators
open Module

noncomputable section

def zspanBasis {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (b : Basis (Fin n) ℝ E) :
    Basis (Fin n) ℤ (Submodule.span ℤ (Set.range b)) :=
  b.restrictScalars ℤ

@[simp] theorem zspanBasis_apply_coe {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (b : Basis (Fin n) ℝ E) (i : Fin n) :
    ((zspanBasis b i : Submodule.span ℤ (Set.range b)) : E) = b i := by
  exact b.restrictScalars_apply ℤ i

end

end Erdos3.BohrLattice.PrimitiveExtension

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCertificate
namespace OAI

section

namespace Erdos3.BohrLattice.BoxCertificate

open scoped BigOperators

def realBox {n : ℕ} (r : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.Icc (-r) r

structure SuccessiveProductCertificate {n : ℕ} (Λ : AddSubgroup (Fin n → ℝ))
    (r : Fin n → ℝ) (B : ℝ) where
  scale : Fin n → ℝ
  point : Fin n → Fin n → ℝ
  scale_nonneg : ∀ i, 0 ≤ scale i
  point_mem : ∀ i, point i ∈ Λ
  independent : LinearIndependent ℝ point
  mem_scaledBox : ∀ i, point i ∈ realBox (scale i • r)
  product_le : ∏ i, scale i ≤ B

end Erdos3.BohrLattice.BoxCertificate

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MinkowskiSecondBox
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate _root_.Set Module Submodule

theorem abs_det_zspan_basis_eq {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (B : Basis (Fin n) ℤ (span ℤ (Set.range b))) :
    |(Matrix.of (((↑) : span ℤ (Set.range b) → (Fin n → ℝ)) ∘ B)).det| =
      |(Matrix.of b).det| := by
  let L : Submodule ℤ (Fin n → ℝ) := span ℤ (Set.range b)
  have hB := ZLattice.covolume_eq_det L B
  have hb := ZLattice.covolume_eq_det L
    (Erdos3.BohrLattice.PrimitiveExtension.zspanBasis b)
  calc
    |(Matrix.of (((↑) : L → (Fin n → ℝ)) ∘ B)).det| =
        ZLattice.covolume L := hB.symm
    _ = |(Matrix.of (((↑) : L → (Fin n → ℝ)) ∘
        Erdos3.BohrLattice.PrimitiveExtension.zspanBasis b)).det| := hb
    _ = |(Matrix.of b).det| := by
      congr 2
      ext i j
      simp [L]

def intCastVec {n : ℕ} (z : Fin n → ℤ) : Fin n → ℝ :=
  fun i ↦ (z i : ℝ)

@[simp] theorem intCastVec_zero {n : ℕ} :
    intCastVec (0 : Fin n → ℤ) = 0 := by
  funext i
  simp [intCastVec]

@[simp] theorem intCastVec_add {n : ℕ} (z w : Fin n → ℤ) :
    intCastVec (z + w) = intCastVec z + intCastVec w := by
  funext i
  simp [intCastVec]

@[simp] theorem intCastVec_smul {n : ℕ} (a : ℤ) (z : Fin n → ℤ) :
    intCastVec (a • z) = (a : ℝ) • intCastVec z := by
  funext i
  simp [intCastVec]

noncomputable def roundedCoefficient (a : ℝ) : ℤ := round a

theorem abs_sub_roundedCoefficient_le_half (a : ℝ) :
    |a - (roundedCoefficient a : ℝ)| ≤ (1 : ℝ) / 2 := by
  simpa [roundedCoefficient] using abs_sub_round a

noncomputable def deleteProjection {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i ↦ x (h.succAbove i) - (x h / v h) * v (h.succAbove i)

noncomputable def deleteProjectionLinear {n : ℕ} (h : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := deleteProjection h v
  map_add' x y := by
    funext i
    simp only [deleteProjection, Pi.add_apply]
    ring
  map_smul' a x := by
    funext i
    simp [deleteProjection]
    ring

@[simp] theorem deleteProjectionLinear_apply {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) :
    deleteProjectionLinear h v x = deleteProjection h v x := rfl

theorem deleteProjection_add_smul {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) (a : ℝ) (hvh : v h ≠ 0) :
    deleteProjection h v (x + a • v) = deleteProjection h v x := by
  funext i
  simp only [deleteProjection, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem abs_apply_le_norm {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have hi := (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mp (le_refl ‖x‖) i
  simpa only [Real.norm_eq_abs] using hi

noncomputable def tailShear {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j ↦
    if j = 0 then (if i = 0 then 1 else 0)
    else if i = 0 then -(B h j / B h 0)
    else if i = j then 1 else 0

@[simp] theorem tailShear_apply_zero_zero {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    tailShear h B 0 0 = 1 := by simp [tailShear]

@[simp] theorem tailShear_apply_succ_zero {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin n) :
    tailShear h B i.succ 0 = 0 := by simp [tailShear]

@[simp] theorem tailShear_apply_zero_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j : Fin n) :
    tailShear h B 0 j.succ = -(B h j.succ / B h 0) := by simp [tailShear]

@[simp] theorem tailShear_apply_succ_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin n) :
    tailShear h B i.succ j.succ = if i = j then 1 else 0 := by
  simp [tailShear]

theorem tailShear_det {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (tailShear h B).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    by_cases hi : i = 0
    · subst i
      simp [tailShear]
    · simp [tailShear, hi]
  · intro i j hji
    have hi0 : i ≠ 0 := by
      intro hi
      subst i
      exact (not_lt_of_ge (Fin.zero_le j)) hji
    have hij : i ≠ j := ne_of_gt hji
    simp [tailShear, hi0, hij]

noncomputable def projectedTail {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ B (h.succAbove i) j.succ -
    (B h j.succ / B h 0) * B (h.succAbove i) 0

theorem mul_tailShear_apply_zero {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    (B * tailShear h B) i 0 = B i 0 := by
  simp [Matrix.mul_apply, tailShear]

theorem mul_tailShear_apply_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (j : Fin n) :
    (B * tailShear h B) i j.succ =
      B i j.succ - (B h j.succ / B h 0) * B i 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, tailShear]
  ring

theorem mul_tailShear_pivot_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hB : B h 0 ≠ 0)
    (j : Fin n) :
    (B * tailShear h B) h j.succ = 0 := by
  rw [mul_tailShear_apply_succ]
  field_simp
  ring

theorem mul_tailShear_minor {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (B * tailShear h B).submatrix h.succAbove Fin.succ = projectedTail h B := by
  ext i j
  simp [projectedTail, mul_tailShear_apply_succ]

theorem abs_det_eq_abs_pivot_mul_abs_det_projectedTail {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hB : B h 0 ≠ 0) :
    |B.det| = |B h 0| * |(projectedTail h B).det| := by
  have hdetC : (B * tailShear h B).det = B.det := by
    simp [Matrix.det_mul, tailShear_det]
  have hminor :
      (B * tailShear h B).submatrix h.succAbove (Fin.succAbove 0) =
        projectedTail h B := by
    simpa using mul_tailShear_minor h B
  have hLaplace := Matrix.det_succ_row (B * tailShear h B) h
  rw [Fin.sum_univ_succ] at hLaplace
  rw [mul_tailShear_apply_zero] at hLaplace
  simp_rw [mul_tailShear_pivot_succ h B hB] at hLaplace
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero] at hLaplace
  rw [hdetC] at hLaplace
  rw [hminor] at hLaplace
  rw [hLaplace, abs_mul, abs_mul]
  simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul]

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MinkowskiSecondBoxGlue
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate _root_.Set Module Submodule

def rawTailLift {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : Fin n → ℤ) : Fin (n + 1) → ℝ :=
  Matrix.mulVec B (Fin.cons 0 (intCastVec z))

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MinkowskiSecondInduction
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiDiagonalNormalization

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate _root_.Set Submodule Module

noncomputable section

def divideCoordinates {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := x i / r i
  invFun x i := x i * r i
  left_inv x := by
    funext i
    exact div_mul_cancel₀ (x i) (hr i).ne'
  right_inv x := by
    funext i
    exact mul_div_cancel_right₀ (x i) (hr i).ne'
  map_add' x y := by
    funext i
    exact add_div (x i) (y i) (r i)
  map_smul' a x := by
    funext i
    simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_assoc]

@[simp] theorem divideCoordinates_apply {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : Fin n → ℝ) (i : Fin n) :
    divideCoordinates r hr x i = x i / r i := rfl

@[simp] theorem divideCoordinates_symm_apply {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : Fin n → ℝ) (i : Fin n) :
    (divideCoordinates r hr).symm x i = x i * r i := rfl

def normalizedBasis {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    Basis (Fin n) ℝ (Fin n → ℝ) :=
  b.map (divideCoordinates r hr)

@[simp] theorem normalizedBasis_apply {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (j i : Fin n) :
    normalizedBasis b r hr j i = b j i / r i := by
  simp [normalizedBasis]

theorem mem_realBox_mul_iff {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (s : ℝ) (_hs : 0 ≤ s) (x : Fin n → ℝ) :
    x ∈ realBox (fun i ↦ s * r i) ↔
      divideCoordinates r hr x ∈ realBox (fun _ ↦ s) := by
  constructor
  · intro hx
    constructor
    · intro i
      apply (le_div_iff₀ (hr i)).2
      simpa [mul_comm] using hx.1 i
    · intro i
      apply (div_le_iff₀ (hr i)).2
      simpa [mul_comm] using hx.2 i
  · intro hx
    constructor
    · intro i
      have hi := (le_div_iff₀ (hr i)).1 (hx.1 i)
      simpa [mul_comm] using hi
    · intro i
      have hi := (div_le_iff₀ (hr i)).1 (hx.2 i)
      simpa [mul_comm] using hi

theorem abs_det_normalizedBasis {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    |(Matrix.of (normalizedBasis b r hr)).det| =
      |(Matrix.of b).det| * (∏ i, r i)⁻¹ := by
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i ↦ (r i)⁻¹)
  have hmatrix : Matrix.of (normalizedBasis b r hr) = Matrix.of b * D := by
    ext j i
    change b j i / r i = ∑ k, b j k * D k i
    rw [Finset.sum_eq_single i]
    · simp [D, div_eq_mul_inv]
    · intro k _ hki
      simp [D, hki]
    · simp
  have hdetD : D.det = (∏ i, r i)⁻¹ := by
    simp [D, Finset.prod_inv_distrib]
  have hprod : 0 < ∏ i, r i := Finset.prod_pos fun i _ ↦ hr i
  rw [hmatrix, Matrix.det_mul, hdetD, abs_mul, abs_inv, abs_of_pos hprod]

theorem divideCoordinates_mem_span_iff {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (x : Fin n → ℝ) :
    divideCoordinates r hr x ∈ Submodule.span ℤ (Set.range (normalizedBasis b r hr)) ↔
      x ∈ Submodule.span ℤ (Set.range b) := by
  let e : (Fin n → ℝ) ≃ₗ[ℤ] (Fin n → ℝ) :=
    (divideCoordinates r hr).restrictScalars ℤ
  have hrange : Set.range (normalizedBasis b r hr) = e '' Set.range b := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨b i, ⟨i, rfl⟩, ?_⟩
      simp [e, normalizedBasis]
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      simp [e, normalizedBasis]
  change e x ∈ Submodule.span ℤ (Set.range (normalizedBasis b r hr)) ↔ _
  rw [hrange]
  exact Submodule.apply_mem_span_image_iff_mem_span e.injective

end

end Erdos3.BohrLattice.MinkowskiDiagonalNormalization

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealDirectionExtension
namespace OAI

section

namespace Erdos3

variable {σ E : Type*} [Fintype σ] [AddCommGroup E] [Module ℚ E] [Module ℝ E]

noncomputable def realDirectionExtension (f : (σ → ℚ) →ₗ[ℚ] E) : (σ → ℝ) →ₗ[ℝ] E := by
  classical
  exact ∑ i, (LinearMap.proj i).smulRight (f (Pi.single i 1))

open scoped Classical in
theorem realDirectionExtension_apply (f : (σ → ℚ) →ₗ[ℚ] E) (h : σ → ℝ) :
    realDirectionExtension f h = ∑ i, h i • f (Pi.single i 1) := by
  classical
  simp only [realDirectionExtension, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]

theorem realDirectionExtension_rat (f : (σ → ℚ) →ₗ[ℚ] E) (h : σ → ℚ) :
    realDirectionExtension f (fun i => (h i : ℝ)) = f h := by
  classical
  rw [realDirectionExtension_apply]
  have he : h = ∑ i, h i • Pi.single i (1 : ℚ) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  exact ratCast_smul_eq ℝ ℚ (h i) _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubquotientEquiv
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℚ E] (P Q : Submodule ℚ E)

abbrev RealSubquotient :=
  @HasQuotient.Quotient (P.baseChange ℝ) (Submodule ℝ (P.baseChange ℝ))
    (@Submodule.hasQuotient ℝ (P.baseChange ℝ) _ _ _)
    ((Q.baseChange ℝ).comap (P.baseChange ℝ).subtype)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixSupInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_det_abs_le_row_bounds (A : Matrix ι ι ℝ) (H : ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ H i) :
    |A.det| ≤ (Fintype.card ι).factorial * ∏ i, H i := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ i, H i := by
      apply Finset.sum_le_sum
      intro σ _
      have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
        rw [← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]
      rw [abs_mul, hsign, one_mul, Finset.abs_prod]
      calc
        _ ≤ ∏ i, H (σ i) :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
        _ = ∏ i, H i := Equiv.prod_comp σ H
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDerivativeBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev BlockParameter (B F α : Type*) := B × F × Option α

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealificationModuleTopology
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realification_moduleTopology_t2 {κ L : Type*} [Fintype κ]
    [AddCommGroup L] [Module ℚ L] (b : Basis κ ℚ L) :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] L)
    T2Space (ℝ ⊗[ℚ] L) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] L)
  have hc : Continuous (b.baseChange ℝ).equivFun :=
    IsModuleTopology.continuous_of_linearMap (b.baseChange ℝ).equivFun.toLinearMap
  exact T2Space.of_injective_continuous (b.baseChange ℝ).equivFun.injective hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev DiagonalAPParameter
    (r N : ℕ) (A : Finset (ZMod N)) :=
  ↥A × (Fin r → ZMod N)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonKernelRangeEquiv
namespace OAI

section

namespace Erdos3

variable {K A B C : Type*} [Field K] [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]

noncomputable def commonKernelRangeEquiv (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (h : LinearMap.ker f = LinearMap.ker g) : LinearMap.range f ≃ₗ[K] LinearMap.range g :=
  f.quotKerEquivRange.symm.trans ((Submodule.quotEquivOfEq _ _ h).trans g.quotKerEquivRange)

noncomputable def commonKernelSubmoduleEquiv (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (U : Submodule K B) (V : Submodule K C)
    (h : LinearMap.ker f = LinearMap.ker g)
    (hf : LinearMap.range f = U) (hg : LinearMap.range g = V) : U ≃ₗ[K] V :=
  (LinearEquiv.ofEq U (LinearMap.range f) hf.symm).trans
    ((commonKernelRangeEquiv f g h).trans (LinearEquiv.ofEq (LinearMap.range g) V hg))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ShortGeneratingBasisBound
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open Module Submodule
open scoped BigOperators

theorem basis_norm_le_of_integral_combination {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) {C : ℝ}
    (hprod : (∏ j, ‖b j‖) ≤ C * |(Matrix.of b).det|)
    (c : Fin n → ℤ) (i : Fin n) (hci : c i ≠ 0) :
    ‖b i‖ ≤ (n.factorial : ℝ) * C * ‖∑ j, c j • b j‖ := by
  classical
  let x := ∑ j, c j • b j
  let H := Function.update (fun j => ‖b j‖) i ‖x‖
  have hentry : ∀ j k, |((Matrix.of b).updateRow i x) j k| ≤ H j := by
    intro j k
    by_cases hji : j = i
    · subst j
      simpa only [Matrix.updateRow_self, H, Function.update_self] using abs_apply_le_norm x k
    · simpa only [Matrix.updateRow_ne hji, Matrix.of_apply, H, Function.update_of_ne hji]
        using abs_apply_le_norm (b j) k
  have hx : x = ∑ j, (c j : ℝ) • b j := by
    simp only [x, Int.cast_smul_eq_zsmul]
  have hdetx : ((Matrix.of b).updateRow i x).det = (c i : ℝ) * (Matrix.of b).det := by
    rw [hx]
    exact Matrix.det_updateRow_sum (Matrix.of b) i (fun j => (c j : ℝ))
  have hH : (∏ j, H j) = ‖x‖ * ∏ j ∈ Finset.univ.erase i, ‖b j‖ := by
    rw [← Finset.mul_prod_erase Finset.univ H (Finset.mem_univ i)]
    rw [show H i = ‖x‖ by simp [H]]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
  have hbound := Erdos3.matrix_det_abs_le_row_bounds ((Matrix.of b).updateRow i x) H hentry
  rw [hdetx, abs_mul, hH, Fintype.card_fin] at hbound
  have hci1 : (1 : ℝ) ≤ |(c i : ℝ)| := by exact_mod_cast Int.one_le_abs hci
  have hdet : 0 < |(Matrix.of b).det| := by
    apply abs_pos.mpr
    have h := (AlternatingMap.map_basis_ne_zero_iff b (Pi.basisFun ℝ (Fin n)).det).mpr
      (Pi.basisFun ℝ (Fin n)).det_ne_zero
    simpa only [Pi.basisFun_det_apply] using h
  have hdetle : |(Matrix.of b).det| ≤
      (n.factorial : ℝ) * (‖x‖ * ∏ j ∈ Finset.univ.erase i, ‖b j‖) := by
    exact (le_mul_of_one_le_left hdet.le hci1).trans hbound
  have hmul : ‖b i‖ * |(Matrix.of b).det| ≤
      ((n.factorial : ℝ) * C * ‖∑ j, c j • b j‖) * |(Matrix.of b).det| := by
    calc
      ‖b i‖ * |(Matrix.of b).det| ≤ ‖b i‖ *
          ((n.factorial : ℝ) * (‖x‖ * ∏ j ∈ Finset.univ.erase i, ‖b j‖)) :=
        mul_le_mul_of_nonneg_left hdetle (norm_nonneg _)
      _ = (n.factorial : ℝ) * ‖x‖ * (∏ j, ‖b j‖) := by
        rw [← Finset.mul_prod_erase Finset.univ (fun j => ‖b j‖) (Finset.mem_univ i)]
        ring
      _ ≤ (n.factorial : ℝ) * ‖x‖ * (C * |(Matrix.of b).det|) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      _ = ((n.factorial : ℝ) * C * ‖∑ j, c j • b j‖) * |(Matrix.of b).det| := by
        dsimp only [x]
        ring
  nlinarith

theorem basis_norm_le_of_short_spanning_family {n : ℕ} {A : Type*}
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) {C R : ℝ} (hC : 0 ≤ C)
    (hprod : (∏ j, ‖b j‖) ≤ C * |(Matrix.of b).det|)
    (v : A → Fin n → ℝ) (hspan : span ℝ (Set.range v) = ⊤)
    (hmem : ∀ a, v a ∈ span ℤ (Set.range b)) (hnorm : ∀ a, ‖v a‖ ≤ R)
    (i : Fin n) : ‖b i‖ ≤ (n.factorial : ℝ) * C * R := by
  classical
  have hex : ∃ a, b.coord i (v a) ≠ 0 := by
    by_contra! h
    have hs : span ℝ (Set.range v) ≤ LinearMap.ker (b.coord i) := by
      apply span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact LinearMap.mem_ker.mpr (h a)
    rw [hspan] at hs
    have hz := LinearMap.mem_ker.mp (hs (show b i ∈ (⊤ : Submodule ℝ (Fin n → ℝ)) from trivial))
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same, one_ne_zero] at hz
  obtain ⟨a, ha⟩ := hex
  have hm := hmem a
  rw [mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  have hci : c i ≠ 0 := by
    intro hz
    apply ha
    rw [← hc, map_sum]
    simp only [map_zsmul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    simp [hz]
  have hb := basis_norm_le_of_integral_combination b hprod c i hci
  rw [hc] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (hnorm a) (mul_nonneg (Nat.cast_nonneg _) hC))

theorem abs_det_eq_of_same_integer_span {n : ℕ}
    (b c : Basis (Fin n) ℝ (Fin n → ℝ))
    (hspan : span ℤ (Set.range b) = span ℤ (Set.range c)) :
    |(Matrix.of b).det| = |(Matrix.of c).det| := by
  have hcov (d : Basis (Fin n) ℝ (Fin n → ℝ)) :
      ZLattice.covolume (span ℤ (Set.range d)) = |(Matrix.of d).det| := by
    simpa only [Function.comp_def, Basis.restrictScalars_apply] using
      ZLattice.covolume_eq_det (span ℤ (Set.range d)) (d.restrictScalars ℤ)
  rw [← hcov b, hspan, hcov c]

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds
namespace OAI

section

namespace Erdos3

open Module

noncomputable def squareGeometryBudget (p : ℝ) : ℝ :=
  ((p + 3) ^ 11 + 2 * p + 5) ^ 11

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeTernaryCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def BinaryTensorIndex (I : Type*) : ℕ → Type _
  | 0 => I
  | n + 1 => BinaryTensorIndex I n × BinaryTensorIndex I n

instance BinaryTensorIndex.fintype (I : Type*) [Fintype I] (n : ℕ) : Fintype (BinaryTensorIndex I n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype I)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (BinaryTensorIndex I n × BinaryTensorIndex I n))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BSGDensity
namespace OAI

section

section BSGCast

namespace NNRat
open scoped _root_.NNRat
variable {K : Type*} [DivisionRing K] [CharZero K]

@[simp] lemma cast_sub {p q : ℚ≥0} (h : p ≤ q) : (↑(q - p) : K) = q - p := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact tsub_add_cancel_of_le h

end NNRat

end BSGCast

section BSGDensity

namespace Finset
open scoped _root_.Finset
variable {K α β : Type*} [DivisionRing K] [CharZero K] [Fintype α] [Fintype β]
  {s t : Finset α} {a : α}

@[simp] lemma dens_product (s : Finset α) (t : Finset β) : (s ×ˢ t).dens = s.dens * t.dens := by
  simp [_root_.Finset.dens, mul_div_mul_comm]

variable [DecidableEq α]

@[grind =]
lemma dens_sdiff_of_subset (h : s ⊆ t) : (t \ s).dens = t.dens - s.dens := by
  suffices (t \ s).dens = (t \ s ∪ s).dens - s.dens by rwa [_root_.Finset.sdiff_union_of_subset h] at this
  rw [_root_.Finset.dens_union_of_disjoint _root_.Finset.sdiff_disjoint, add_tsub_cancel_right]

lemma cast_dens_inter : ((s ∩ t).dens : K) = s.dens + t.dens - (s ∪ t).dens := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact _root_.Finset.dens_inter_add_dens_union ..

lemma cast_dens_sdiff (h : s ⊆ t) : ((t \ s).dens : K) = t.dens - s.dens := by
  rw [dens_sdiff_of_subset h, NNRat.cast_sub (_root_.Finset.dens_mono h)]

end Finset

end BSGDensity

end

end OAI
end


