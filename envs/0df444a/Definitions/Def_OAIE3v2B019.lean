-- Prove2me | Definitions.Def_OAIE3v2B019
-- name    : OAIE3v2B019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:58:42.813908+00:00
-- url     : https://prove2.me/theorems/8f644f18-e4f9-4185-af30-47ead745dc8f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 20 of 311
-- statement:
--   Definitions bundle 20 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/NativeHorizontalLiftBudget.lean`, `Dynamics/PointwiseSymbolBudget.lean`, `Estimates/DerivativeHorizontalLifts.lean`, `Estimates/EuclideanGraphResidual.lean`, `Estimates/FirstCoefficientDerivativeBounds.lean`, `Estimates/LinearDerivativeRemoval.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/RationalLieSubalgebra.lean`, `Estimates/RealSubspaceIntersectionCorrections.lean`, `Estimates/ReducedSymbolDimensions.lean`, `Estimates/ReindexedDerivativePoints.lean`, `Estimates/SortedPositiveWeights.lean`, `Estimates/StepDropTerminalContainment.lean`, `Estimates/WeightedLinearBounds.lean`, `Geometry/ControlledSumCoordinates.lean`, `Geometry/DerivativeVerticalCoordinates.lean`, `Geometry/FilteredSubalgebraCoordinates.lean`, `Geometry/ProductEuclideanCoordinates.lean`, `Geometry/RealFastCoefficientCoordinates.lean`, `Lattices/EuclideanDerivativeLattice.lean`, `Lattices/ScaledLatticeCovolume.lean`, `Lattices/UniformDerivativeLatticeExtraction.lean`, `Linear/AugmentedMatrixSection.lean`, `Linear/BaseChangeCoordinateProjection.lean`, `Linear/BasisImageSection.lean`, `Linear/FullFastHorizontalSpanning.lean`, `Linear/LayerOneCoefficientBasis.lean`, `Linear/RationalSpanCoordinates.lean`, `Linear/RationalTagConstraintChartBasis.lean`, `Linear/RealDualRationalBounds.lean`, `Linear/SortedBasisTriangular.lean`, `Linear/SplitPreimageSpanning.lean`, `Linear/SynchronizeSplittingProjection.lean`, `Sampling/DerivativeGridPoints.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalLieSubalgebra
namespace OAI

section

namespace Erdos3

open Module

variable {ι η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem lie_lowerCentralSeries_eq_bot_of_injective {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ M M s = ⊥ := by
  apply LieIdeal.bot_of_map_eq_bot hφ
  apply le_antisymm _ bot_le
  rw [← hnil]
  exact LieIdeal.map_lowerCentralSeries_le s

theorem lie_subalgebra_lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (K : LieSubalgebra ℚ L) :
    LieModule.lowerCentralSeries ℚ K K s = ⊥ :=
  lie_lowerCentralSeries_eq_bot_of_injective K.incl (fun _ _ h => Subtype.ext h) hnil

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductEuclideanCoordinates
namespace OAI

section

namespace Erdos3

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

noncomputable def productEuclideanEquiv :
    ((σ → ℝ) × (κ → ℝ)) ≃ₗ[ℝ] EuclideanSpace ℝ (σ ⊕ κ) :=
  (LinearEquiv.sumArrowLequivProdArrow σ κ ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (σ ⊕ κ) ℝ).symm.toLinearEquiv

omit [Fintype σ] [Fintype κ] in
@[simp] theorem productEuclideanEquiv_apply_inl (x : (σ → ℝ) × (κ → ℝ)) (i : σ) :
    productEuclideanEquiv x (Sum.inl i) = x.1 i := rfl

omit [Fintype σ] [Fintype κ] in
@[simp] theorem productEuclideanEquiv_apply_inr (x : (σ → ℝ) × (κ → ℝ)) (j : κ) :
    productEuclideanEquiv x (Sum.inr j) = x.2 j := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DerivativeGridPoints
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {σ κ : Type*} [Fintype κ]

noncomputable def derivativeGridPoint (T : σ → ℝ) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (h : σ → ℤ) (r : κ → ℝ) : (σ → ℝ) × (κ → ℝ) :=
  (fun i => (h i : ℝ) / T i, fun j => scale j * (Y (fun i => (h i : ℝ)) - M *ᵥ r) j)

theorem derivativeGridPoint_bound [Fintype σ] (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (scale : κ → ℝ) (hscale : ∀ j, 0 < scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (h : σ → ℤ) (r e : κ → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : ∀ i, |(h i : ℝ)| ≤ A * T i)
    (heq : Y (fun i => (h i : ℝ)) = e + M *ᵥ r)
    (he : ∀ j, |e j| ≤ B / scale j) :
    ‖derivativeGridPoint T scale Y M h r‖ ≤ max A B := by
  have hv : Y (fun i => (h i : ℝ)) - M *ᵥ r = e := by rw [heq, add_sub_cancel_right]
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (hA.trans (le_max_left _ _))).mpr
    intro i
    change ‖(h i : ℝ) / T i‖ ≤ max A B
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hT i)]
    exact ((div_le_iff₀ (hT i)).mpr (hh i)).trans (le_max_left _ _)
  · apply (pi_norm_le_iff_of_nonneg (hB.trans (le_max_right _ _))).mpr
    intro j
    change ‖scale j * (Y (fun i => (h i : ℝ)) - M *ᵥ r) j‖ ≤ max A B
    rw [hv, Real.norm_eq_abs, abs_mul, abs_of_pos (hscale j)]
    have hj : scale j * |e j| ≤ B := by
      simpa only [mul_comm] using (le_div_iff₀ (hscale j)).mp (he j)
    exact hj.trans (le_max_right _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EuclideanDerivativeLattice
namespace OAI

section

namespace Erdos3

noncomputable def coordinateScaleEquiv {ι : Type*} (d : ι → ℝ) (hd : ∀ i, d i ≠ 0) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) where
  toFun x i := d i * x i
  invFun x i := x i / d i
  left_inv x := by funext i; exact mul_div_cancel_left₀ (x i) (hd i)
  right_inv x := by funext i; exact mul_div_cancel₀ (x i) (hd i)
  map_add' x y := by funext i; exact mul_add _ _ _
  map_smul' c x := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem coordinateScaleEquiv_apply {ι : Type*} (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (x : ι → ℝ) (i : ι) : coordinateScaleEquiv d hd x i = d i * x i := rfl

@[simp] theorem coordinateScaleEquiv_symm_apply {ι : Type*} (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (x : ι → ℝ) (i : ι) : (coordinateScaleEquiv d hd).symm x i = x i / d i := rfl

noncomputable def derivativeShearEquiv {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (Y : E →ₗ[ℝ] F) (A : F ≃ₗ[ℝ] F) :
    (E × F) ≃ₗ[ℝ] (E × F) where
  toFun x := (x.1, Y x.1 - A x.2)
  invFun x := (x.1, A.symm (Y x.1 - x.2))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by
    refine Prod.ext ?_ ?_
    · rfl
    · change Y (x.1 + y.1) - A (x.2 + y.2) = (Y x.1 - A x.2) + (Y y.1 - A y.2)
      rw [map_add, map_add]
      abel
  map_smul' c x := by
    refine Prod.ext ?_ ?_
    · rfl
    · change Y (c • x.1) - A (c • x.2) = c • (Y x.1 - A x.2)
      rw [map_smul, map_smul, smul_sub]

@[simp] theorem derivativeShearEquiv_apply {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (Y : E →ₗ[ℝ] F) (A : F ≃ₗ[ℝ] F) (x : E × F) :
    derivativeShearEquiv Y A x = (x.1, Y x.1 - A x.2) := rfl

noncomputable def derivativeLatticeEquiv {σ κ : Type*}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) :
    ((σ → ℝ) × (κ → ℝ)) ≃ₗ[ℝ] ((σ → ℝ) × (κ → ℝ)) :=
  ((LinearEquiv.refl ℝ (σ → ℝ)).prodCongr
    (coordinateScaleEquiv (fun _ : κ => (l : ℝ)⁻¹) (fun _ => inv_ne_zero (by exact_mod_cast hl.ne')))).trans
    ((derivativeShearEquiv Y A).trans
      ((coordinateScaleEquiv (fun i => (T i)⁻¹) (fun i => inv_ne_zero (hT i))).prodCongr
        (coordinateScaleEquiv scale hscale)))

theorem derivativeLatticeEquiv_apply {σ κ : Type*}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (x : (σ → ℝ) × (κ → ℝ)) :
    derivativeLatticeEquiv T hT scale hscale Y A l hl x =
      (fun i => x.1 i / T i, fun j => scale j * (Y x.1 - A (fun k => x.2 k / l)) j) := by
  simp only [derivativeLatticeEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, derivativeShearEquiv_apply]
  refine Prod.ext ?_ ?_
  · funext i
    simp only [coordinateScaleEquiv_apply, div_eq_mul_inv, mul_comm]
  · funext j
    have he : coordinateScaleEquiv (fun _ : κ => (l : ℝ)⁻¹)
        (fun _ => inv_ne_zero (by exact_mod_cast hl.ne')) x.2 = (fun k => x.2 k / l) := by
      funext k
      simp only [coordinateScaleEquiv_apply, div_eq_mul_inv, mul_comm]
    exact congrArg (fun v : κ → ℝ => scale j * (Y x.1 - A v) j) he

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

noncomputable def standardProductBasis :
    Basis (σ ⊕ κ) ℝ ((σ → ℝ) × (κ → ℝ)) :=
  (Pi.basisFun ℝ σ).prod (Pi.basisFun ℝ κ)

variable (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

noncomputable def derivativeLatticeBasis : Basis (σ ⊕ κ) ℝ ((σ → ℝ) × (κ → ℝ)) :=
  standardProductBasis.map (derivativeLatticeEquiv T hT scale hscale Y A l hl)

noncomputable def derivativeLattice : Submodule ℤ ((σ → ℝ) × (κ → ℝ)) :=
  Submodule.span ℤ (Set.range (derivativeLatticeBasis T hT scale hscale Y A l hl))

end Erdos3

end

section

namespace Erdos3

open Module

variable {σ κ : Type*} [Fintype σ] [Fintype κ]
  (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

noncomputable def euclideanDerivativeLatticeBasis :
    Basis (σ ⊕ κ) ℝ (EuclideanSpace ℝ (σ ⊕ κ)) :=
  (derivativeLatticeBasis T hT scale hscale Y A l hl).map productEuclideanEquiv

noncomputable def euclideanDerivativeLattice : Submodule ℤ (EuclideanSpace ℝ (σ ⊕ κ)) :=
  Submodule.span ℤ (Set.range (euclideanDerivativeLatticeBasis T hT scale hscale Y A l hl))

instance euclideanDerivativeLattice_discrete :
    DiscreteTopology (euclideanDerivativeLattice T hT scale hscale Y A l hl) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ
    (Set.range (euclideanDerivativeLatticeBasis T hT scale hscale Y A l hl))))

theorem euclideanDerivativeLattice_mem_iff (v : EuclideanSpace ℝ (σ ⊕ κ)) :
    v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl ↔
      productEuclideanEquiv.symm v ∈ derivativeLattice T hT scale hscale Y A l hl := by
  change v ∈ Submodule.span ℤ (Set.range
    ((derivativeLatticeBasis T hT scale hscale Y A l hl).map productEuclideanEquiv)) ↔ _
  rw [← ZSpan.map]
  constructor
  · rintro ⟨x, hx, hxv⟩
    change productEuclideanEquiv x = v at hxv
    rw [← hxv, LinearEquiv.symm_apply_apply]
    exact hx
  · intro hv
    exact ⟨productEuclideanEquiv.symm v, hv, productEuclideanEquiv.apply_symm_apply v⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalSpanCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

omit [Fintype ι] in
theorem span_conditional_basis (e : Basis ι ℚ L) (S : Set ι) [DecidablePred (· ∈ S)] :
    Submodule.span ℚ (Set.range (fun i => if i ∈ S then e i else 0)) =
      Submodule.span ℚ (e '' S) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (if i ∈ S then e i else 0) ∈ _
    split_ifs with h
    · exact Submodule.subset_span ⟨i, h, rfl⟩
    · exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    apply Submodule.subset_span
    exact ⟨i, by simp only [hi, ↓reduceIte]⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeHorizontalLiftBudget
namespace OAI

section

namespace Erdos3

def absorbedInitialParameter (p : ℝ) : ℝ :=
  3 * p + 1 + (p + 2) ^ 36 + (p + 2) ^ 19

theorem absorbedInitialParameter_bounds {p : ℝ} (hp : 0 ≤ p) :
    p ≤ absorbedInitialParameter p ∧
    Real.exp p + Real.exp p * Real.exp ((p + 2) ^ 19) * Real.exp p ≤
      Real.exp (absorbedInitialParameter p) ∧
    Real.exp p * (Real.exp p * (Real.exp p * Real.exp ((p + 2) ^ 36))) ≤
      Real.exp (absorbedInitialParameter p) := by
  have h19 : 0 ≤ (p + 2) ^ 19 := by positivity
  have h36 : 0 ≤ (p + 2) ^ 36 := by positivity
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  refine ⟨by unfold absorbedInitialParameter; linarith, ?_, ?_⟩
  · calc
      _ = Real.exp p + Real.exp (2 * p + (p + 2) ^ 19) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (2 * p + (p + 2) ^ 19) + Real.exp (2 * p + (p + 2) ^ 19) := by
        gcongr
        linarith
      _ = 2 * Real.exp (2 * p + (p + 2) ^ 19) := (two_mul _).symm
      _ ≤ Real.exp 1 * Real.exp (2 * p + (p + 2) ^ 19) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (1 + (2 * p + (p + 2) ^ 19)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold absorbedInitialParameter; linarith)
  · rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold absorbedInitialParameter
    linarith

theorem absorbedInitialParameter_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ absorbedInitialParameter p := hp.trans (absorbedInitialParameter_bounds hp).1

end Erdos3

end

section

namespace Erdos3

def extractedInitialParameter (p : ℝ) : ℝ := (p + 2) ^ 3 + 3 * p + 3

theorem extractedInitialParameter_controls {p : ℝ} (hp : 0 ≤ p) :
    p ≤ extractedInitialParameter p ∧ 3 * p ≤ extractedInitialParameter p ∧
      (p + 2) ^ 3 ≤ extractedInitialParameter p := by
  have h : 0 ≤ (p + 2) ^ 3 := by positivity
  unfold extractedInitialParameter
  exact ⟨by linarith, by linarith, by linarith⟩

theorem extractedInitialParameter_products {p B C : ℝ} (hp : 0 ≤ p)
    (hB : 0 ≤ B) (hBp : B ≤ Real.exp p) (hC : 0 ≤ C) (hCp : C ≤ Real.exp p)
    (δ l : ℕ) (hδ : (δ : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ B ^ 2) :
    B * C ≤ Real.exp (extractedInitialParameter p) ∧
      ((δ * l : ℕ) : ℝ) ≤ Real.exp (extractedInitialParameter p) := by
  have hq := (extractedInitialParameter_controls hp).2.1
  constructor
  · calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hBp hCp hC (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * (Real.exp p) ^ 2 := by
        apply mul_le_mul hδ _ (Nat.cast_nonneg _) (Real.exp_nonneg _)
        exact hl.trans (pow_le_pow_left₀ hB hBp 2)
      _ = Real.exp (3 * p) := by rw [pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PointwiseSymbolBudget
namespace OAI

section

namespace Erdos3

theorem symbol_spanning_parameter_ge (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ (p + (s + 3)) ^ (s + 3) := by
  apply (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ s + 3)).trans
  simpa only [pow_one] using pow_le_pow_right₀
    (by have := Nat.cast_nonneg (α := ℝ) s; linarith : (1 : ℝ) ≤ p + (s + 3))
    (by omega : 1 ≤ s + 3)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisImageSection
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_normalized_basis_vector {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (g : E →ₗ[K] (ι → K))
    (B : Matrix ι (Fin k) K) (hB : ∀ i j, B i j = g (b j) i)
    (N : Matrix (Fin k) (Fin k) K) (j : Fin k) :
    ∃ v : E, g v = (B * N).col j := by
  refine ⟨∑ t, N t j • b t, ?_⟩
  funext i
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ t, N t j * g (b t) i) = ∑ t, B i t * N t j
  apply Finset.sum_congr rfl
  intro t _
  rw [hB, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScaledLatticeCovolume
namespace OAI

section

namespace Erdos3

open Module

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]
  (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))

noncomputable def latticeKernel : Submodule ℤ (LinearMap.ker π) :=
  ZLattice.comap ℝ Λ (LinearMap.ker π).subtype

instance latticeKernel_discrete [DiscreteTopology Λ] : DiscreteTopology (latticeKernel Λ π) :=
  ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanGraphResidual
namespace OAI

section

namespace Erdos3

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

noncomputable def euclideanDerivativeShiftMap (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) :
    EuclideanSpace ℝ (σ ⊕ κ) →ₗ[ℝ] (σ → ℝ) :=
  (coordinateScaleEquiv T hT).toLinearMap.comp
    ((LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DerivativeVerticalCoordinates
namespace OAI

section

namespace Erdos3

noncomputable def euclideanVerticalMap {σ κ : Type*}
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) :
    (κ → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (σ ⊕ κ) :=
  productEuclideanEquiv.toLinearMap.comp ((LinearMap.inr ℝ (σ → ℝ) (κ → ℝ)).comp
    ((coordinateScaleEquiv scale hscale).toLinearMap.comp A.toLinearMap))

@[simp] theorem euclideanVerticalMap_apply_inl {σ κ : Type*}
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (x : κ → ℝ) (i : σ) :
    euclideanVerticalMap (σ := σ) scale hscale A x (Sum.inl i) = 0 := rfl

@[simp] theorem euclideanVerticalMap_apply_inr {σ κ : Type*}
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (x : κ → ℝ) (j : κ) :
    euclideanVerticalMap (σ := σ) scale hscale A x (Sum.inr j) = scale j * A x j := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealDualRationalBounds
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

def dualStructureConstants (c : ι → ι → ι → ℚ) : (ι ⊕ ι) → (ι ⊕ ι) → (ι ⊕ ι) → ℚ
  | Sum.inl i, Sum.inl j, Sum.inl k => c i j k
  | Sum.inl i, Sum.inr j, Sum.inr k => c i j k
  | Sum.inr i, Sum.inl j, Sum.inr k => c i j k
  | _, _, _ => 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem real_baseChange_ker {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℚ V] [Module ℚ W] (f : V →ₗ[ℚ] W) :
    (LinearMap.ker f).baseChange ℝ = LinearMap.ker (f.baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact (Module.Flat.ker_lTensor_eq ℝ ℝ f).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearDerivativeRemoval
namespace OAI

section

namespace Erdos3

variable {R E K : Type*} [Field R] [AddCommGroup E] [Module R E]
  [AddCommGroup K] [Module R K]

theorem linear_action_triple {G : Type*} [Group G] (ρ : G →* (E ≃ₗ[R] E))
    (a b c : G) (x : E) : ρ (a * b * c) x = ρ a (ρ b (ρ c x)) := by
  rw [map_mul, map_mul]
  rfl

theorem linear_cocycle_triple {G : Type*} [Group G] (ρ : G →* (E ≃ₗ[R] E))
    (Y : G → E) (hY : ∀ a b, Y (a * b) = Y a + ρ a (Y b)) (a b c : G) :
    Y (a * b * c) = Y a + ρ a (Y b) + ρ a (ρ b (Y c)) := by
  rw [hY, hY, map_mul]
  rfl

theorem linear_derivative_remove (a b f g : E ≃ₗ[R] E)
    (hcomp : ∀ x, f x = a (g (b x)))
    (y ya yn yb s r z : E)
    (hprod : y = ya + a yn + a (g yb)) (hsystem : y = s + f r + z) :
    yn = a.symm (s - ya) + g (b r - yb) + a.symm z := by
  apply a.injective
  simp only [map_add, map_sub, LinearEquiv.apply_symm_apply]
  calc
    a yn = y - ya - a (g yb) := by rw [hprod]; abel
    _ = _ := by rw [hsystem, hcomp]; abel

theorem linear_lift_remove (a b f g : E ≃ₗ[R] E)
    (hcomp : ∀ x, f x = a (g (b x))) (S T : K →ₗ[R] E)
    (hST : S = f.toLinearMap.comp T) :
    a.symm.toLinearMap.comp S = g.toLinearMap.comp (b.toLinearMap.comp T) := by
  apply LinearMap.ext
  intro x
  change a.symm (S x) = g (b (T x))
  rw [hST]
  change a.symm (f (T x)) = _
  rw [hcomp, LinearEquiv.symm_apply_apply]

theorem linear_derivative_absorb (f : E →ₗ[R] E) (S T : K →ₗ[R] E)
    (hST : S = f.comp T) (y s r : E) (k ks kr : K)
    (hsystem : y = s + f r + S k) :
    y = (s - S ks) + f (r - T kr) + S (k + ks + kr) := by
  rw [hsystem]
  simp only [map_add, map_sub]
  have hkr : S kr = f (T kr) := DFunLike.congr_fun hST kr
  rw [hkr]
  abel

theorem horizontal_lift_remove {H : Type*} [AddCommGroup H] [Module R H]
    (P : E →ₗ[R] H) (a b : E ≃ₗ[R] E)
    (ha : ∀ x, P (a x) = P x) (hb : ∀ x, P (b x) = P x)
    (S T : K →ₗ[R] E) (ι : K →ₗ[R] H)
    (hS : P.comp S = ι) (hT : P.comp T = ι) :
    P.comp (a.symm.toLinearMap.comp S) = ι ∧
      P.comp (b.toLinearMap.comp T) = ι := by
  constructor
  · apply LinearMap.ext
    intro x
    change P (a.symm (S x)) = ι x
    have h := ha (a.symm (S x))
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm.trans (DFunLike.congr_fun hS x)
  · apply LinearMap.ext
    intro x
    change P (b (T x)) = ι x
    rw [hb]
    exact DFunLike.congr_fun hT x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SortedBasisTriangular
namespace OAI

section

namespace Erdos3

open Module

theorem basis_reindex_equivFun {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [Fintype ι]
    (b : Basis ι K E) (e : Equiv.Perm ι) (x : E) :
    (b.reindex e.symm).equivFun x = fun i => b.equivFun x (e i) := by
  funext i
  simp only [Basis.equivFun_apply, Basis.repr_reindex_apply, Equiv.symm_symm]

theorem basis_reindex_toMatrix {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K E) (e : Equiv.Perm ι) (f : E →ₗ[K] E) (i j : ι) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) f i j =
      LinearMap.toMatrix b b f (e i) (e j) := by
  simp only [LinearMap.toMatrix_apply, Basis.repr_reindex_apply, Basis.reindex_apply,
    Equiv.symm_symm]

theorem basis_coordinate_linearEquiv_matrix {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K E) (f : E ≃ₗ[K] E) :
    LinearMap.toMatrix' (b.equivFun.symm.trans (f.trans b.equivFun)).toLinearMap =
      LinearMap.toMatrix b b f.toLinearMap := by
  ext i j
  rw [LinearMap.toMatrix'_apply, LinearMap.toMatrix_apply]
  change b.equivFun (f (b.equivFun.symm (Pi.single j 1))) i = b.repr (f (b j)) i
  have he : b.equivFun.symm (Pi.single j 1) = b j := by
    apply b.equivFun.injective
    simp only [b.equivFun.apply_symm_apply]
    funext i
    simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
  rw [he, Basis.equivFun_apply]

end Erdos3

end

section

namespace Erdos3

open Module

theorem sorted_basis_upper_zero {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] {d : ℕ}
    (b : Basis (Fin d) K E) (w : Fin d → ℕ) (f : E →ₗ[K] E)
    (hf : ∀ i j, w i ≤ w j → LinearMap.toMatrix b b f i j = (1 : Matrix (Fin d) (Fin d) K) i j)
    (e : Equiv.Perm (Fin d)) (hm : Monotone (w ∘ e)) (i j : Fin d) (hij : i < j) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) f i j = 0 := by
  rw [basis_reindex_toMatrix, hf _ _ (hm hij.le)]
  simp only [Matrix.one_apply, e.injective.eq_iff, if_neg (ne_of_lt hij)]

theorem sorted_basis_diagonal_one {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] {d : ℕ}
    (b : Basis (Fin d) K E) (w : Fin d → ℕ) (f : E →ₗ[K] E)
    (hf : ∀ i j, w i ≤ w j → LinearMap.toMatrix b b f i j = (1 : Matrix (Fin d) (Fin d) K) i j)
    (e : Equiv.Perm (Fin d)) (i : Fin d) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) f i i = 1 := by
  rw [basis_reindex_toMatrix, hf _ _ le_rfl, Matrix.one_apply_eq]

theorem sorted_basis_initial_identity {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] {d a : ℕ}
    (b : Basis (Fin d) K E) (w : Fin d → ℕ) (f : E →ₗ[K] E)
    (hf : ∀ i j, w i ≤ w j → LinearMap.toMatrix b b f i j = (1 : Matrix (Fin d) (Fin d) K) i j)
    (e : Equiv.Perm (Fin d)) (hfirst : ∀ i, i.val < a → w (e i) = 1)
    (i j : Fin d) (hi : i.val < a) (hj : j.val < a) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) f i j =
      (1 : Matrix (Fin d) (Fin d) K) i j := by
  rw [basis_reindex_toMatrix, hf _ _ (by rw [hfirst i hi, hfirst j hj])]
  simp only [Matrix.one_apply, e.injective.eq_iff]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledSumCoordinates
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem real_column_span_fromCols {ι κ ν : Type*}
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) :
    Submodule.span ℝ (Set.range ((Matrix.fromCols A B).map (Rat.castHom ℝ)).col) =
      Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) ⊔
        Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) := by
  rw [Matrix.fromCols_map]
  have hr : Set.range (Matrix.fromCols (A.map (Rat.castHom ℝ)) (B.map (Rat.castHom ℝ))).col =
      Set.range (A.map (Rat.castHom ℝ)).col ∪ Set.range (B.map (Rat.castHom ℝ)).col := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      cases j with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr j => exact Or.inr ⟨j, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr j, rfl⟩
  rw [hr, Submodule.span_union]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem pi_norm_restriction_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (f : κ → ι) : ‖x ∘ f‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  exact norm_le_pi_norm x (f i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubspaceIntersectionCorrections
namespace OAI

section

namespace Erdos3

theorem norm_removed_derivative_bound {E V : Type*}
    [AddCommGroup E] [Module ℝ E] [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (N : E →ₗ[ℝ] V) (A : E →ₗ[ℝ] E) (x y : E)
    (C M D T : ℝ) (hC : 0 ≤ C) (hT : 0 < T)
    (hA : ∀ z, ‖N (A z)‖ ≤ C * ‖N z‖)
    (hx : ‖N x‖ ≤ M / T) (hy : ‖N y‖ ≤ D / T) :
    ‖N (A (x - y))‖ ≤ C * (M + D) / T := by
  calc
    _ ≤ C * ‖N (x - y)‖ := hA _
    _ ≤ C * (‖N x‖ + ‖N y‖) := by
      rw [map_sub]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hC
    _ ≤ C * (M / T + D / T) := mul_le_mul_of_nonneg_left (add_le_add hx hy) hC
    _ = _ := by field_simp [hT.ne']

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

theorem horizontal_absorption_with_split {H E : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]
    (U K : Submodule ℝ H) (P : E →ₗ[ℝ] H)
    (f : E →ₗ[ℝ] E) (hf : P.comp f = P) (S R : K →ₗ[ℝ] E)
    (hSR : S = f.comp R) (hS : P.comp S = K.subtype) (hR : P.comp R = K.subtype)
    (split : H →ₗ[ℝ] K) (hsplit : ∀ x, x ∈ U ⊔ K → x - (split x).val ∈ U)
    (y small rational : E) (k : K) (hsystem : y = small + f rational + S k)
    (hy : P y ∈ U) (hsmall : P small ∈ U ⊔ K) (hrational : P rational ∈ U ⊔ K) :
    let ks := split (P small)
    let kr := split (P rational)
    P (small - S ks) ∈ U ∧ P (rational - R kr) ∈ U ∧ (k + ks + kr).val ∈ U ∧
      y = (small - S ks) + f (rational - R kr) + S (k + ks + kr) := by
  let ks := split (P small)
  let kr := split (P rational)
  have hs : P (small - S ks) ∈ U := by
    rw [map_sub, show P (S ks) = ks.val from DFunLike.congr_fun hS ks]
    exact hsplit (P small) hsmall
  have hr : P (rational - R kr) ∈ U := by
    rw [map_sub, show P (R kr) = kr.val from DFunLike.congr_fun hR kr]
    exact hsplit (P rational) hrational
  have hnew := linear_derivative_absorb f S R hSR y small rational k ks kr hsystem
  refine ⟨hs, hr, ?_, hnew⟩
  have he : P y = P (small - S ks) + P (rational - R kr) + (k + ks + kr).val := by
    rw [hnew, map_add, map_add,
      show P (f (rational - R kr)) = P (rational - R kr) from DFunLike.congr_fun hf _,
      show P (S (k + ks + kr)) = (k + ks + kr).val from DFunLike.congr_fun hS _]
  have hm := U.sub_mem (U.sub_mem hy hs) hr
  have he' : P y - P (small - S ks) - P (rational - R kr) = (k + ks + kr).val := by
    rw [he]
    abel
  exact he' ▸ hm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SortedPositiveWeights
namespace OAI

section

namespace Erdos3

theorem exists_sorted_positive_weights {d : ℕ} (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i) :
    ∃ (e : Equiv.Perm (Fin d)) (a : ℕ), a ≤ d ∧ Monotone (w ∘ e) ∧
      ∀ i, i.val < a ↔ w (e i) = 1 := by
  classical
  let e := Tuple.sort w
  let a := (Finset.univ.filter (fun i => w (e i) ≤ 1)).card
  have hm : Monotone (w ∘ e) := Tuple.monotone_sort w
  refine ⟨e, a, ?_, hm, ?_⟩
  · exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin d)
  · intro i
    have hi : i.val < a ↔ w (e i) ≤ 1 :=
      Tuple.lt_card_le_iff_apply_le_of_monotone hm
    exact hi.trans ⟨fun h => Nat.le_antisymm h (hw (e i)), fun h => h.le⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepDropTerminalContainment
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

abbrev StepDropRow (υ χ κ ν : Type*) := υ ⊕ χ ⊕ (κ × ν) ⊕ ν

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintChartBasis
namespace OAI

section

namespace Erdos3

theorem basis_projection_range_eq_span {E ι κ : Type*}
    [AddCommGroup E] [Module ℝ E] (b : Module.Basis κ ℝ E)
    (P : E →ₗ[ℝ] (ι → ℝ)) :
    LinearMap.range P = Submodule.span ℝ (Set.range (fun j => P (b j))) := by
  rw [← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
  rfl

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
  (e : Basis ι ℚ V) (K : Submodule ℚ V) (b : Basis κ ℚ K)

noncomputable def submoduleBasisMatrix : Matrix ι κ ℚ :=
  fun i j => e.repr (b j).val i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeHorizontalLifts
namespace OAI

section

namespace Erdos3

theorem exists_basis_linear_lift {K E F G ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
    [AddCommGroup G] [Module K G]
    (b : Module.Basis ι K E) (f : E →ₗ[K] F) (W : G →ₗ[K] F)
    (v : ι → G) (hrep : ∀ j, f (b j) = W (v j)) :
    ∃ g : E →ₗ[K] G, (∀ j, g (b j) = v j) ∧ W.comp g = f := by
  refine ⟨b.constr K v, fun j => b.constr_basis K v j, ?_⟩
  apply b.ext
  intro j
  change W ((b.constr K v) (b j)) = f (b j)
  rw [Module.Basis.constr_basis]
  exact (hrep j).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedLinearBounds
namespace OAI

section

namespace Erdos3

open Module

theorem weighted_linear_bound_of_unit {E F ι κ : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (e : Basis ι ℝ E) (f : Basis κ ℝ F) (W : ι → ℝ) (V : κ → ℝ)
    (Φ : E →ₗ[ℝ] F) (C : ℝ)
    (hΦ : ∀ x, (∀ i, |e.repr x i| ≤ 1 / W i) → ∀ j, |f.repr (Φ x) j| ≤ C / V j)
    {M : ℝ} (hM : 0 ≤ M) (x : E) (hx : ∀ i, |e.repr x i| ≤ M / W i) :
    ∀ j, |f.repr (Φ x) j| ≤ C * M / V j := by
  by_cases hzero : M = 0
  · have hxi : x = 0 := by
      apply e.repr.injective
      ext i
      have hi : |e.repr x i| ≤ 0 := by simpa only [hzero, zero_div] using hx i
      simpa only [map_zero, Finsupp.zero_apply] using (abs_nonpos_iff.mp hi)
    intro j
    simp only [hxi, map_zero, Finsupp.zero_apply, abs_zero, hzero, mul_zero, zero_div, le_refl]
  · have hpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    let y : E := M⁻¹ • x
    have hy : ∀ i, |e.repr y i| ≤ 1 / W i := by
      intro i
      change |e.repr (M⁻¹ • x) i| ≤ _
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
      calc
        _ ≤ M⁻¹ * (M / W i) := mul_le_mul_of_nonneg_left (hx i) (inv_pos.mpr hpos).le
        _ = _ := by field_simp
    have hxy : x = M • y := by simp only [y, smul_smul, mul_inv_cancel₀ hzero, one_smul]
    intro j
    rw [hxy, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hpos]
    calc
      _ ≤ M * (C / V j) := mul_le_mul_of_nonneg_left (hΦ y hy j) hM
      _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BaseChangeCoordinateProjection
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem baseChange_coordinate_eq
    {V W ι κ : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (b : Basis ι ℚ V) (c : Basis κ ℚ W) (P : V →ₗ[ℚ] W) (r : κ → ι)
    (hP : ∀ x i, c.repr (P x) i = b.repr x (r i))
    (x : ℝ ⊗[ℚ] V) (i : κ) :
    (c.baseChange ℝ).repr (P.baseChange ℝ x) i = (b.baseChange ℝ).repr x (r i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul t x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, hP]

theorem baseChange_coordinate_projector_repr
    {V W ι : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (b : Basis ι ℚ V) (P : V →ₗ[ℚ] W) (S : W →ₗ[ℚ] V)
    (p : ι → Prop) [DecidablePred p]
    (hproj : ∀ x i, b.repr (S (P x)) i = if p i then b.repr x i else 0)
    (x : ℝ ⊗[ℚ] V) (i : ι) :
    (b.baseChange ℝ).repr (S.baseChange ℝ (P.baseChange ℝ x)) i =
      if p i then (b.baseChange ℝ).repr x i else 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply] at *
    rw [hx, hy]
    split_ifs <;> simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, hproj]
    split_ifs <;> simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FirstCoefficientDerivativeBounds
namespace OAI

section

namespace Erdos3

theorem realLinearMap_eq_of_rat_directions {σ E : Type*} [Fintype σ]
    [AddCommGroup E] [Module ℝ E] (f g : (σ → ℝ) →ₗ[ℝ] E)
    (h : ∀ v : σ → ℚ, f (fun i => (v i : ℝ)) = g (fun i => (v i : ℝ))) : f = g := by
  classical
  apply (Pi.basisFun ℝ σ).ext
  intro i
  have he : (fun j => ((Pi.single i (1 : ℚ) : σ → ℚ) j : ℝ)) = Pi.basisFun ℝ σ i := by
    funext j
    by_cases hij : j = i <;> simp [Pi.basisFun_apply, hij]
  simpa only [he] using h (Pi.single i 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedSymbolDimensions
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*}
  [Fintype σ]
  [Fintype ι]
  [LieRing L]
  [LieAlgebra ℚ L]
  {s : ℕ}
  (e : Basis ι ℚ L)
  (ω : ι → ℕ)
  (w : σ → ℕ)
  (hw : ∀ i, 0 < w i)

def reducedMatrixParameter (s : ℕ) (p : ℝ) : ℝ :=
  3 * (p + (s + 2)) ^ (s + 2) * (p + 1) + 2 * p + 2

theorem reducedMatrixParameter_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reducedMatrixParameter s p := by
  unfold reducedMatrixParameter
  positivity

theorem le_reducedMatrixParameter (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ reducedMatrixParameter s p := by
  have h : 0 ≤ 3 * (p + (s + 2)) ^ (s + 2) * (p + 1) := by positivity
  unfold reducedMatrixParameter
  linarith

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReindexedDerivativePoints
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem pi_norm_comp_equiv {ι : Type*} [Fintype ι] (x : ι → ℝ) (e : Equiv.Perm ι) :
    ‖x ∘ e‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact norm_le_pi_norm x (e i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have h := norm_le_pi_norm (x ∘ e) (e.symm i)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h

theorem derivativeGridPoint_reindex {σ κ : Type*} [Fintype κ]
    (T : σ → ℝ) (scale : κ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ))
    (A : Matrix κ κ ℝ) (e : Equiv.Perm κ) (h : σ → ℤ) (r : κ → ℝ) :
    derivativeGridPoint T (scale ∘ e) ((LinearMap.funLeft ℝ ℝ e).comp Y)
      (A.submatrix e e) h (r ∘ e) =
        ((derivativeGridPoint T scale Y A h r).1, (derivativeGridPoint T scale Y A h r).2 ∘ e) := by
  have hm : (A.submatrix e e) *ᵥ (r ∘ e) = (A *ᵥ r) ∘ e := by
    simp only [Matrix.submatrix_mulVec_equiv, Function.comp_def, Equiv.apply_symm_apply]
  apply Prod.ext
  · rfl
  · funext i
    change scale (e i) * (Y (fun j => (h j : ℝ)) (e i) - ((A.submatrix e e) *ᵥ (r ∘ e)) i) =
      scale (e i) * (Y (fun j => (h j : ℝ)) (e i) - (A *ᵥ r) (e i))
    rw [hm]
    rfl

theorem derivativeGridPoint_reindex_norm {σ κ : Type*} [Fintype σ] [Fintype κ]
    (T : σ → ℝ) (scale : κ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ))
    (A : Matrix κ κ ℝ) (e : Equiv.Perm κ) (h : σ → ℤ) (r : κ → ℝ) :
    ‖derivativeGridPoint T (scale ∘ e) ((LinearMap.funLeft ℝ ℝ e).comp Y)
      (A.submatrix e e) h (r ∘ e)‖ = ‖derivativeGridPoint T scale Y A h r‖ := by
  rw [derivativeGridPoint_reindex, Prod.norm_def, Prod.norm_def, pi_norm_comp_equiv]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FilteredSubalgebraCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def subalgebraLayerFamily (e : Basis ι ℚ L) (v : κ → L)
    (ω : ι → ℕ) (j : ℕ) : κ ⊕ ι → L :=
  Sum.elim v (fun i => if j ≤ ω i then e i else 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AugmentedMatrixSection
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {ι κ μ R : Type*} [CommRing R]

def constraintProjectionMatrix (Q : Matrix ι κ R) (P : Matrix μ κ R) :
    Matrix (ι ⊕ μ) κ R := fun i j => Sum.elim (fun k => Q k j) (fun k => P k j) i

def constraintProjectionInput (y : μ → R) : (ι ⊕ μ) → R := Sum.elim (fun _ => 0) y

theorem mulVec_constraintProjectionInput [Fintype ι] [Fintype μ]
    (S : Matrix κ (ι ⊕ μ) R) (y : μ → R) :
    S *ᵥ constraintProjectionInput (ι := ι) y = (fun i j => S i (Sum.inr j)) *ᵥ y := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, constraintProjectionInput]

theorem constraintProjectionInput_weighted {δ : Type*}
    (r : ι → δ) (c : μ → δ) (W : δ → ℝ) (hW : ∀ d, 0 < W d)
    {M : ℝ} (hM : 0 ≤ M) (y : μ → ℝ) (hy : ∀ i, |y i| ≤ M / W (c i)) :
    ∀ i, |constraintProjectionInput (ι := ι) y i| ≤ M / W (Sum.elim r c i) := by
  intro i
  cases i with
  | inl i =>
    change |(0 : ℝ)| ≤ M / W (r i)
    rw [abs_zero]
    exact div_nonneg hM (hW _).le
  | inr i => exact hy i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SynchronizeSplittingProjection
namespace OAI

section

namespace Erdos3

variable {G Q : Type*} [Group G] [Group Q]

theorem synchronize_splitting_projection (q : G →* Q) (H : Subgroup G)
    (E P R a d : G) (A D : Q) (hP : P ∈ H) (ha : a ∈ H) (hd : d ∈ H)
    (haq : q a = A⁻¹ * q E) (hdq : q d = q R * D⁻¹) :
    (E * a⁻¹) * (a * P * d) * (d⁻¹ * R) = E * P * R ∧
      a * P * d ∈ H ∧ q (E * a⁻¹) = A ∧ q (d⁻¹ * R) = D ∧
      q (a * P * d) = A⁻¹ * q (E * P * R) * D⁻¹ := by
  refine ⟨?_, H.mul_mem (H.mul_mem ha hP) hd, ?_, ?_, ?_⟩
  · group
  · rw [map_mul, map_inv, haq]
    group
  · rw [map_mul, map_inv, hdq]
    group
  · simp only [map_mul, haq, hdq]
    group

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealFastCoefficientCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {K E H : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup H] [Module K H] {a d : ℕ}

def extendInitialCoordinates : (Fin a → K) →ₗ[K] (Fin d → K) where
  toFun x j := if h : j.val < a then x ⟨j.val, h⟩ else 0
  map_add' x y := by funext j; by_cases h : j.val < a <;> simp [h]
  map_smul' c x := by funext j; by_cases h : j.val < a <;> simp [h]

@[simp] theorem extendInitialCoordinates_castLE (ha : a ≤ d) (x : Fin a → K) (i : Fin a) :
    extendInitialCoordinates x (Fin.castLE ha i) = x i := by
  simp [extendInitialCoordinates, i.isLt]

end Erdos3

end

section

namespace Erdos3

theorem norm_extendInitialCoordinates_le {a d : ℕ} (x : Fin a → ℝ) :
    ‖(extendInitialCoordinates x : Fin d → ℝ)‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  change ‖if hi : i.val < a then x ⟨i.val, hi⟩ else 0‖ ≤ ‖x‖
  split_ifs with hi
  · exact norm_le_pi_norm x ⟨i.val, hi⟩
  · simpa only [norm_zero] using norm_nonneg x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformDerivativeLatticeExtraction
namespace OAI

section

namespace Erdos3

theorem derivative_output_exponent_le {p : ℝ} (hp : 0 ≤ p) :
    4 * p ^ 2 + 4 * p + 1 ≤ (p + 2) ^ 3 := by
  nlinarith [pow_nonneg hp 3]

theorem derivative_projection_budget_le_exp (n : ℕ) (R δ p : ℝ)
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hR0 : 0 ≤ R) (hR : R ≤ Real.exp p)
    (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp p) :
    (3 * R) ^ (n - 1) / δ ≤ Real.exp ((p + 2) ^ 3) := by
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hbase : 3 * R ≤ Real.exp (p + 2) := by
    calc
      _ ≤ Real.exp 2 * Real.exp p := mul_le_mul hthree hR hR0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hn' : ((n - 1 : ℕ) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Nat.sub_le n 1)).trans hn
  calc
    _ ≤ Real.exp (p + 2) ^ (n - 1) * Real.exp p := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase _) hδinv
        (inv_nonneg.mpr hδ.le) (by positivity)
    _ = Real.exp (((n - 1 : ℕ) : ℝ) * (p + 2) + p) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (p ^ 2 + 3 * p) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hn' (by positivity : 0 ≤ p + 2)]
    _ ≤ Real.exp ((p + 2) ^ 3) := by
      apply Real.exp_le_exp.mpr
      nlinarith [derivative_output_exponent_le hp, sq_nonneg p]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LayerOneCoefficientBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  {s : ℕ}
  (e : Basis ι ℚ L)
  (ω : ι → ℕ)

abbrev LayerOneBasisIndex (ω : ι → ℕ) := {i : ι // ¬ 2 ≤ ω i}

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SplitPreimageSpanning
namespace OAI

section

namespace Erdos3

variable {R V W ι κ : Type*} [Field R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem comap_eq_section_image_sup_kernel (P : V →ₗ[R] W) (S : W →ₗ[R] V)
    (hS : ∀ x, P (S x) = x) (U : Submodule R W) :
    U.comap P = U.map S ⊔ LinearMap.ker P := by
  ext x
  constructor
  · intro hx
    apply Submodule.mem_sup.mpr
    refine ⟨S (P x), ⟨P x, hx, rfl⟩, x - S (P x), ?_, ?_⟩
    · change P (x - S (P x)) = 0
      rw [map_sub, hS, sub_self]
    · abel
  · intro hx
    obtain ⟨a, ⟨y, hy, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    change P (S y + b) ∈ U
    rw [map_add, hS, show P b = 0 from hb, add_zero]
    exact hy

theorem span_range_sumElim (v : ι → V) (w : κ → V) :
    Submodule.span R (Set.range (Sum.elim v w)) =
      Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range w) := by
  have he : Set.range (Sum.elim v w) = Set.range v ∪ Set.range w := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact Or.inl ⟨i, rfl⟩
      | inr i => exact Or.inr ⟨i, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr i, rfl⟩
  rw [he, Submodule.span_union]

theorem split_preimage_spanning (P : V →ₗ[R] W) (S : W →ₗ[R] V)
    (hS : ∀ x, P (S x) = x) (U : Submodule R W)
    (v : ι → W) (hv : Submodule.span R (Set.range v) = U)
    (k : κ → V) (hk : Submodule.span R (Set.range k) = LinearMap.ker P) :
    Submodule.span R (Set.range (Sum.elim (fun i => S (v i)) k)) = U.comap P := by
  rw [span_range_sumElim, hk, comap_eq_section_image_sup_kernel P S hS, ← hv,
    Submodule.map_span]
  congr 1
  exact congrArg (Submodule.span R) (Set.range_comp S v)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FullFastHorizontalSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  {s : ℕ}
  (e : Basis ι ℚ L)
  (ω : ι → ℕ)

abbrev TopGradedBasisIndex (s : ℕ) (ω : ι → ℕ) := {i : ι // s + 1 ≤ ω i}

end Erdos3.NilpotentLieFiltration

end

end OAI
end


