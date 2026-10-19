-- Prove2me | Definitions.Def_OAIE3v2B155
-- name    : OAIE3v2B155
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:25:09.902971+00:00
-- url     : https://prove2.me/theorems/c5dbf96c-12ed-438f-82d3-c73c5f68bc9a
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 157 of 311
-- statement:
--   Definitions bundle 157 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B141`, `OAIE3v2B142`, `OAIE3v2B143`, `OAIE3v2B144`, `OAIE3v2B145` of this split.
--
--   Modules: `Estimates/FastHorizontalFactorization.lean`, `Estimates/FormalCurrentInputBounds.lean`, `Estimates/FormalHorizontalReabsorption.lean`, `Estimates/FormalInductionTerminal.lean`, `Estimates/RealFirstCoefficientHorizontal.lean`, `Estimates/ReducedRelativeCoefficientBounds.lean`, `Linear/FormalKernelAbsorption.lean`, `Linear/LayerOneCoefficientBasis.lean`, `Linear/RationalSpanDerivativeSystem.lean`, `Linear/RationalTagConstraintChartBasis.lean`, `Nilpotent/BracketArrayEquation.lean`, `Nilpotent/UniformControlledBracketStage.lean`, `Polynomial/FirstCoefficientPolynomialDerivative.lean`, `Polynomial/FormalPolynomialCorrectionStep.lean`, `Polynomial/PolynomialLiftArrays.lean`, `Polynomial/QuantitativeOuterPolynomialProducts.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B141
import Definitions.Def_OAIE3v2B142
import Definitions.Def_OAIE3v2B143
import Definitions.Def_OAIE3v2B144
import Definitions.Def_OAIE3v2B145

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFirstCoefficientHorizontal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def realFirstCoefficientHorizontalSection :
    (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) →ₗ[ℝ] F.RealFirstCoefficientModule w :=
  (F.firstCoefficientRealEquiv w).toLinearMap.comp ((F.firstCoefficientHorizontalSection w).baseChange ℝ)

theorem realFirstCoefficientHorizontal_section (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.realFirstCoefficientHorizontal w (F.realFirstCoefficientHorizontalSection w x) = x := by
  change (F.firstCoefficientHorizontal w).baseChange ℝ
    ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w
      ((F.firstCoefficientHorizontalSection w).baseChange ℝ x))) = x
  rw [LinearEquiv.symm_apply_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r v => rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, F.firstCoefficientHorizontal_section]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem mem_coefficient_sup_polynomialLayer {s : ℕ} (F : NilpotentLieFiltration L s)
    (V : Submodule ℚ L) (j : ℕ) (P : VectorPolynomial σ ℚ L) :
    P ∈ coefficientSubmodule V ⊔ F.polynomialFiltration.layer j ↔
      ∀ α, coefficients P α ∈ V ⊔ F.layer j := by
  rw [polynomialLayer_eq_coefficientSubmodule, ← coefficientSubmodule_sup]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem exists_formal_polynomial_product_bound (s a k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∀ rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot), rs.length ≤ k →
      (∀ r ∈ rs, r.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
      (∀ r ∈ rs, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) r.coord) →
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) rs.prod.coord := by
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_slow_product_bound s a k
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure T hT rs hlen hadapted hbound
  obtain ⟨xs, hxs⟩ := F.realification.exists_adapted_polynomial_list_lift (fun _ => 1) rs hadapted
  have hxlen : xs.length ≤ k := by simpa only [← hxs, List.length_map] using hlen
  have hxbound : ∀ x ∈ xs, F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + 2) ^ a)) x := by
    intro x hx
    have hmem : F.realification.adaptedFullPolynomialHom (fun _ => 1) x ∈ rs := by
      rw [← hxs]
      exact List.mem_map_of_mem hx
    exact (F.polynomialSlowBound_iff_formal b _ T _ x).mpr (hbound _ hmem)
  have hout := (F.polynomialSlowBound_iff_formal b _ T _ xs.prod).mp (
    hprod F b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) H p hH hp hι hσ hHp hstructure
      T hT xs hxlen hxbound)
  rwa [map_list_prod, hxs] at hout

theorem exists_formal_polynomial_product_grid (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot), rs.length ≤ k →
        (∀ r ∈ rs, r.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ r ∈ rs, CoefficientGrid (b.baseChange ℝ) l r.coord) →
        CoefficientGrid (b.baseChange ℝ) m rs.prod.coord := by
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_rational_product_bound s k
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨m, hm, hmp, hlm, hgrid⟩ :=
    hprod F b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) H p hH hp hι hσ hHp hstructure l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro rs hlen hadapted hbound
  obtain ⟨xs, hxs⟩ := F.realification.exists_adapted_polynomial_list_lift (fun _ => 1) rs hadapted
  have hxlen : xs.length ≤ k := by simpa only [← hxs, List.length_map] using hlen
  have hxgrid : ∀ x ∈ xs, F.PolynomialRationalGrid b (fun _ => 1) l x := by
    intro x hx
    have hmem : F.realification.adaptedFullPolynomialHom (fun _ => 1) x ∈ rs := by
      rw [← hxs]
      exact List.mem_map_of_mem hx
    exact (F.polynomialRationalGrid_iff_formal b _ l x).mpr (hbound _ hmem)
  have hout := (F.polynomialRationalGrid_iff_formal b _ m xs.prod).mp (hgrid xs hxlen hxgrid)
  rwa [map_list_prod, hxs] at hout

end Erdos3.NilpotentLieFiltration

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

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

def horizontalCoefficientIndex (w : σ → ℕ) (i : LayerOneBasisIndex ω) :
    FirstCoefficientIndex w ω :=
  ⟨(0, i.val), by
    have hp := F.adaptedBasis_weight_pos e ω hF i.val
    have hi := i.property
    simp only [map_zero, Nat.zero_add]
    omega⟩

def layerOneIndexOfConstant (w : σ → ℕ) (z : FirstCoefficientIndex w ω)
    (hz : z.val.1 = 0) : LayerOneBasisIndex ω :=
  ⟨z.val.2, by
    have h := z.property
    rw [hz, map_zero] at h
    omega⟩

theorem horizontalCoefficientIndex_of_constant (w : σ → ℕ)
    (z : FirstCoefficientIndex w ω) (hz : z.val.1 = 0) :
    F.horizontalCoefficientIndex e ω hF w (layerOneIndexOfConstant ω w z hz) = z := by
  apply Subtype.ext
  exact Prod.ext hz.symm rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem coefficient_common_derivative_difference [Fintype σ]
    (V : Submodule ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1)))
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (h h₀ : σ → ℝ)
    (S S₀ R R₀ Z : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hh : F.realFirstCoefficientDirectionMap B.coord h -
      (S + F.realFirstCoefficientAdjoint (fun _ => 1) B R + Z) ∈ V)
    (hh₀ : F.realFirstCoefficientDirectionMap B.coord h₀ -
      (S₀ + F.realFirstCoefficientAdjoint (fun _ => 1) B R₀ + Z) ∈ V) :
    F.realFirstCoefficientDirectionMap B.coord (h - h₀) -
      ((S - S₀) + F.realFirstCoefficientAdjoint (fun _ => 1) B (R - R₀)) ∈ V := by
  have hd := V.sub_mem hh hh₀
  rw [map_sub, map_sub]
  convert hd using 1; abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def coefficientSlowCorrection
    (A : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (h : σ → ℝ)
    (ε u : F.RealFirstCoefficientModule (fun _ : σ => 1)) :
    F.RealFirstCoefficientModule (fun _ : σ => 1) :=
  F.realFirstCoefficientAdjoint (fun _ => 1) A⁻¹
    (ε + u - F.realFirstCoefficientDirectionMap A.coord h)

noncomputable def coefficientGridCorrection
    (D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (h : σ → ℝ)
    (μ v : F.RealFirstCoefficientModule (fun _ : σ => 1)) :
    F.RealFirstCoefficientModule (fun _ : σ => 1) :=
  v + F.realFirstCoefficientAdjoint (fun _ => 1) D μ - F.realFirstCoefficientDirectionMap D.coord h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalInductionTerminal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem FormalCorrectionProperty.mul
    {L μ σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
    {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} (hgraded : BasisHomogeneousBrackets b w)
    {A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot}
    (hA : F.FormalCorrectionProperty b w U A) (hB : F.FormalCorrectionProperty b w U B) :
    F.FormalCorrectionProperty b w U (A * B) := by
  refine ⟨?_, ?_, ?_⟩
  · let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
      { U.toSubmodule.restrictScalars ℚ with lie_mem' := U.lie_mem }
    exact lieBCH_mem (coefficientLieSubalgebra Uq) s hA.1 hB.1
  · exact lieBCH_mem
      (gradedPolynomialSubalgebra (b.baseChange ℝ) w (hgraded.baseChange b w) (fun _ : σ => 1))
      s hA.2.1 hB.2.1
  · have h := eval_lieBCH (fun _ : σ => (0 : ℚ)) s A.coord B.coord
    simp only [eval_zero_eq_coefficient, hA.2.2, hB.2.2] at h
    change coefficients (lieBCH s A.coord B.coord) 0 = 0
    rw [h]
    change ((1 : F.realification.Group) * 1).coord = 0
    rw [one_mul]
    rfl

theorem FormalCorrectionProperty.list_prod
    {L μ σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
    {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} (hgraded : BasisHomogeneousBrackets b w)
    (rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot))
    (hrs : ∀ r ∈ rs, F.FormalCorrectionProperty b w U r) :
    F.FormalCorrectionProperty b w U rs.prod := by
  induction rs with
  | nil =>
    refine ⟨?_, (gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)).zero_mem, ?_⟩
    · intro α
      change coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈ U
      simp only [map_zero, Finsupp.zero_apply, zero_mem]
    · change coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0
      simp only [map_zero, Finsupp.zero_apply]
  | cons r rs ih =>
    exact (hrs r List.mem_cons_self).mul hgraded (ih (fun x hx => hrs x (List.mem_cons_of_mem r hx)))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintChartBasis
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {κ V : Type*} [AddCommGroup V] [Module ℚ V]
  (K : Submodule ℚ V) (b : Basis κ ℚ K)

variable [Fintype κ]

noncomputable def realSubmoduleParameterization : (κ → ℝ) ≃ₗ[ℝ] K.baseChange ℝ :=
  (realSubmoduleBasis K b).equivFun.symm

theorem realSubmoduleParameterization_basis (i : κ) :
    realSubmoduleParameterization K b (Pi.basisFun ℝ κ i) = realSubmoduleBasis K b i := by
  classical
  apply (realSubmoduleBasis K b).equivFun.injective
  rw [realSubmoduleParameterization, LinearEquiv.apply_symm_apply]
  ext j
  simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
  (e : Basis ι ℚ V) (K : Submodule ℚ V) (b : Basis κ ℚ K)

theorem realSubmoduleBasis_matrix_coordinates (j : κ) :
    (e.baseChange ℝ).equivFun (realSubmoduleBasis K b j).val =
      ((submoduleBasisMatrix e K b).map (Rat.castHom ℝ)).col j := by
  funext i
  rw [Basis.equivFun_apply, realSubmoduleBasis_coe, Basis.baseChange_repr_tmul]
  simp [submoduleBasisMatrix, Matrix.col, Algebra.smul_def]

theorem realSubmoduleBasis_matrix_span :
    Submodule.span ℝ (Set.range ((submoduleBasisMatrix e K b).map (Rat.castHom ℝ)).col) =
      (K.baseChange ℝ).map (e.baseChange ℝ).equivFun.toLinearMap := by
  let f := (e.baseChange ℝ).equivFun.toLinearMap.comp (K.baseChange ℝ).subtype
  have he : (f ∘ realSubmoduleBasis K b) =
      ((submoduleBasisMatrix e K b).map (Rat.castHom ℝ)).col := by
    funext j
    exact realSubmoduleBasis_matrix_coordinates e K b j
  have hs := congrArg (fun U : Submodule ℝ (K.baseChange ℝ) => U.map f)
    (realSubmoduleBasis K b).span_eq
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, he] at hs
  exact hs.trans (by simp only [f, LinearMap.range_comp, Submodule.range_subtype])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalSpanDerivativeSystem
namespace OAI

section

namespace Erdos3

open Module

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

theorem basisWeightedCoordinates_norm_le_euclidean [Fintype ι]
    (b : Basis ι ℝ E) (scale : ι → ℝ) (x : E) :
    ‖basisWeightedCoordinates b scale x‖ ≤
      ‖(EuclideanSpace.equiv ι ℝ).symm (basisWeightedCoordinates b scale x)‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le
    ((EuclideanSpace.equiv ι ℝ).symm (basisWeightedCoordinates b scale x)) i

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem transport_coordinate_derivatives_to_rational_span
    {σ E V : Type*} [Fintype σ] [DecidableEq σ]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℚ V]
    {a d : ℕ} (ha : a ≤ d) (b : Basis (Fin d) ℝ E)
    (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] V)) (P : E →ₗ[ℝ] (ℝ ⊗[ℚ] V))
    (hP : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = P x)
    (T : σ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] E) (f : E ≃ₗ[ℝ] E)
    (scale : Fin d → ℝ) (bound : ℝ)
    (D : CoordinateDerivativeSystem ha T (b.equivFun.toLinearMap.comp Y)
      (b.equivFun.symm.trans (f.trans b.equivFun)) scale bound)
    (K : Submodule ℚ V) (bK : Basis (Fin D.k) ℚ K)
    (hspan : D.K.map η.toLinearMap = K.baseChange ℝ)
    (hbasis : ∀ j, (1 : ℝ) ⊗ₜ[ℚ] (bK j : V) = η ((D.basisMatrix.map (Rat.castHom ℝ)).col j)) :
    ∃ S R : (K.baseChange ℝ) →ₗ[ℝ] E,
      S = f.toLinearMap.comp R ∧ P.comp S = (K.baseChange ℝ).subtype ∧
      P.comp R = (K.baseChange ℝ).subtype ∧
      (∀ x, ‖basisWeightedCoordinates b scale (S x)‖ ≤ bound * ‖η.symm x.val‖) ∧
      (∀ j, b.equivFun (R (realSubmoduleBasis K bK j)) ∈ realDenominatorGrid D.liftDenominator) ∧
      ∃ (small rational : σ → E) (k : σ → K.baseChange ℝ),
        (∀ i, Y (Pi.single i 1) = small i + f (rational i) + S (k i)) ∧
        (∀ i, b.equivFun (rational i) ∈ realDenominatorGrid D.derivativeDenominator) ∧
        (∀ i, ‖basisWeightedCoordinates b scale (small i)‖ ≤ bound / T i) := by
  have hraw := transport_coordinate_derivative_system ha b η P hP T Y f scale bound D
  obtain ⟨_, R₀, S₀, hSR₀, hR₀, hS₀, hnorm₀, hgrid₀, hsystem₀⟩ := hraw
  let eK : (K.baseChange ℝ) ≃ₗ[ℝ] D.K.map η.toLinearMap :=
    LinearEquiv.ofEq _ _ hspan.symm
  have heK (x : K.baseChange ℝ) : (eK x).val = x.val :=
    LinearEquiv.coe_ofEq_apply hspan.symm x
  let S := S₀.comp eK.toLinearMap
  let R := R₀.comp eK.toLinearMap
  have hSR : S = f.toLinearMap.comp R := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hSR₀ (eK x)
  have hS : P.comp S = (K.baseChange ℝ).subtype := by
    apply LinearMap.ext
    intro x
    exact (hS₀ (eK x)).trans (heK x)
  have hR : P.comp R = (K.baseChange ℝ).subtype := by
    apply LinearMap.ext
    intro x
    exact (hR₀ (eK x)).trans (heK x)
  refine ⟨S, R, hSR, hS, hR, ?_, ?_, ?_⟩
  · intro x
    have h := (basisWeightedCoordinates_norm_le_euclidean b scale (S x)).trans (hnorm₀ (eK x))
    simpa only [heK] using h
  · intro j
    obtain ⟨x, hx, hg⟩ := hgrid₀ j
    have he : eK (realSubmoduleBasis K bK j) = x := by
      apply Subtype.ext
      exact (heK _).trans ((realSubmoduleBasis_coe K bK j).trans ((hbasis j).trans hx.symm))
    exact (congrArg (fun z => b.equivFun (R₀ z) ∈ realDenominatorGrid D.liftDenominator) he).mpr hg
  · choose small rational k₀ hsystem hgrid hsmall using hsystem₀
    refine ⟨small, rational, fun i => eK.symm (k₀ i), ?_, hgrid, ?_⟩
    · intro i
      have he : S (eK.symm (k₀ i)) = S₀ (k₀ i) :=
        congrArg S₀ (eK.apply_symm_apply (k₀ i))
      have hi : Pi.basisFun ℝ σ i = (Pi.single i 1 : σ → ℝ) := Pi.basisFun_apply ℝ σ i
      exact (congrArg Y hi).symm.trans
        ((hsystem i).trans (congrArg (fun z => small i + f (rational i) + z) he.symm))
    · intro i
      exact (basisWeightedCoordinates_norm_le_euclidean b scale (small i)).trans (hsmall i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastHorizontalFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def realLayerOneLieSection :
    (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) →ₗ[ℝ] (ℝ ⊗[ℚ] L) :=
  (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i} (hF 2)).baseChange ℝ

theorem realLayerOneLieSection_rightInverse (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    (F.layer 2).mkQ.baseChange ℝ (F.realLayerOneLieSection e ω hF x) = x :=
  realSupportedQuotientSection_rightInverse e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x

theorem realLayerOneLieSection_coordinate_zero
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (i : ι) (hi : 2 ≤ ω i) :
    (e.baseChange ℝ).repr (F.realLayerOneLieSection e ω hF x) i = 0 :=
  realSupportedQuotientSection_coordinate_zero e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x i hi

variable [Fintype σ]

noncomputable def layerOnePolynomialCorrection (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
  F.realification.linearPolynomialGroup (fun i => F.realLayerOneLieSection e ω hF (a i))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def realLayerOneCorrection (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.RealAdaptedPolynomialGroup (fun _ : σ => 1) :=
  F.realAdaptedPolynomialGroupLift (fun _ => 1) e ω hF (F.layerOnePolynomialCorrection e ω hF a)

theorem realLayerOneCorrection_realize (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.realAdaptedPolynomialGroupHom (fun _ => 1) (F.realLayerOneCorrection e ω hF a) =
      F.layerOnePolynomialCorrection e ω hF a :=
  F.realAdaptedPolynomialGroupHom_lift (fun _ => 1) e ω hF _

theorem realLayerOneCorrection_log (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.realAdaptedPolynomialMap (fun _ => 1) (F.realLayerOneCorrection e ω hF a).coord =
      linearPolynomial (fun i => F.realLayerOneLieSection e ω hF (a i)) := by
  have he := congrArg (fun g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group =>
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) (F.realLayerOneCorrection_realize e ω hF a)
  exact he

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable def realPointwisePolynomialSubgroup : Subgroup (F.RealAdaptedPolynomialGroup w) :=
  (show Subgroup (F.RealPolynomialSymbolGroup w) from
    realLieSubgroup (realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF w U))).comap
      ((F.realPolynomialSymbolHom e ω hF w).comp (F.realAdaptedPolynomialGroupHom w))

theorem mem_realPointwisePolynomialSubgroup (g : F.RealAdaptedPolynomialGroup w) :
    g ∈ F.realPointwisePolynomialSubgroup e ω hF w U ↔
      F.realExtendedSymbolMap w g.coord ∈
        realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF w U) := by
  change F.realSymbolOfPolynomial e ω hF w (F.realAdaptedPolynomialMap w g.coord) ∈
    realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF w U) ↔ _
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialLiftArrays
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

open VectorPolynomial

variable {σ κ ι L : Type*} [Fintype κ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {V : Submodule ℚ L}

theorem bracket_system_matches_lift_array (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (A : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (h : map ((realBracketSystem f k).restrictScalars ℚ) A = liftQuotientArray f S) :
    ∀ t α, coefficients (S t - ⁅A, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) α ∈ V.baseChange ℝ := by
  intro t α
  apply (realQuotientCoordinateMap_eq_zero_iff f _).mp
  funext i
  have hi := congrArg (fun P : VectorPolynomial σ ℚ (κ × ι → ℝ) => coefficients P α (t, i)) h
  simp only [coefficients_map, LinearMap.restrictScalars_apply,
    coefficients_liftQuotientArray, realBracketSystem_apply] at hi
  rw [map_sub, Finsupp.sub_apply, coefficients_lie_constant, map_sub, Pi.sub_apply]
  exact sub_eq_zero.mpr hi.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BracketArrayEquation
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {σ κ ι L : Type*} [Fintype κ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {V : Submodule ℚ L}

theorem liftQuotientArray_neg (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    liftQuotientArray f (fun t => -S t) = -liftQuotientArray f S := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  funext bi
  simp only [coefficients_liftQuotientArray, map_neg, Finsupp.neg_apply, Pi.neg_apply]

theorem liftQuotientArray_norm_bound (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hS : ∀ t, ‖realQuotientCoordinateMap f (coefficients (S t) α)‖ ≤ M) :
    ‖coefficients (liftQuotientArray f S) α‖ ≤ M := by
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro bi
  rw [coefficients_liftQuotientArray]
  exact (norm_le_pi_norm (realQuotientCoordinateMap f (coefficients (S bi.1) α)) bi.2).trans (hS bi.1)

theorem liftQuotientArray_grid (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ) (l : ℕ)
    (hS : ∀ t, realQuotientCoordinateMap f (coefficients (S t) α) ∈ realDenominatorGrid l) :
    coefficients (liftQuotientArray f S) α ∈ realDenominatorGrid l := by
  classical
  have hex : ∀ t, ∃ z : ι → ℤ,
      (fun i => (z i : ℝ)) = (l : ℝ) • realQuotientCoordinateMap f (coefficients (S t) α) := hS
  choose z hz using hex
  refine ⟨fun bi => z bi.1 bi.2, ?_⟩
  funext bi
  change (z bi.1 bi.2 : ℝ) = (l : ℝ) * coefficients (liftQuotientArray f S) α bi
  rw [coefficients_liftQuotientArray]
  exact congrFun (hz bi.1) bi.2

theorem bracket_array_equation_of_current_relation
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) (π : (ℝ ⊗[ℚ] L) →ₗ[ℝ] (ℝ ⊗[ℚ] L))
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hcurrent : ∀ t α, ⁅coefficients P α, (1 : ℝ) ⊗ₜ[ℚ] k t⁆ -
      (π (coefficients (S t) α) - π (coefficients (R t) α)) ∈ V.baseChange ℝ) :
    ∀ α, realBracketSystem f k (coefficients P α) =
      coefficients (liftQuotientArray f (fun t => map (π.restrictScalars ℚ)
        (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)))) α +
      coefficients (liftQuotientArray f (fun t => map (π.restrictScalars ℚ)
        (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))) α := by
  intro α
  funext bi
  have hi := congrFun ((realQuotientCoordinateMap_eq_zero_iff f _).mpr (hcurrent bi.1 α)) bi.2
  simp only [map_sub, Pi.sub_apply, Pi.zero_apply] at hi
  change realQuotientCoordinateMap f ⁅coefficients P α, (1 : ℝ) ⊗ₜ[ℚ] k bi.1⁆ bi.2 = _
  simp only [Pi.add_apply, coefficients_liftQuotientArray, coefficients_map,
    LinearMap.restrictScalars_apply, map_neg, map_sub, Finsupp.sub_apply,
    Finsupp.neg_apply, Pi.sub_apply, Pi.neg_apply]
  linear_combination hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalCurrentInputBounds
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem projected_lift_residual_eq {σ μ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
    (b : Basis μ ℝ L) (w : μ → ℕ) {j : ℕ} (hj : j ≠ 1)
    (S : VectorPolynomial σ ℚ L) (k : L) (hk : basisGradeProjection b w 1 k = k) :
    map ((basisGradeProjection b w j).restrictScalars ℚ) (S - monomial 0 k) =
      map ((basisGradeProjection b w j).restrictScalars ℚ) S := by
  have hz := basisGradeProjection_other b w hj k
  rw [hk] at hz
  rw [map_sub, map_monomial]
  change map ((basisGradeProjection b w j).restrictScalars ℚ) S -
    monomial 0 (basisGradeProjection b w j k) = _
  rw [hz]
  simp only [monomial, TensorProduct.tmul_zero, sub_zero]

variable {σ κ ι μ L : Type*} [Fintype κ] [Fintype ι] [Fintype μ]
  [LieRing L] [LieAlgebra ℚ L] {V : Submodule ℚ L}

theorem projected_lift_array_bound (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) {j H : ℕ} (hj : 2 ≤ j)
    (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k t) =
      (1 : ℝ) ⊗ₜ[ℚ] k t)
    (hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ t α, ‖(b.baseChange ℝ).equivFun (coefficients (S t) α)‖ ≤ M / monomialScale T α) :
    ∀ α, ‖coefficients (liftQuotientArray f (fun t =>
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
          (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)))) α‖ ≤
      (((Fintype.card μ : ℝ) + 1) * (H + 1)) * M / monomialScale T α := by
  intro α
  let C : ℝ := ((Fintype.card μ : ℝ) + 1) * (H + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply liftQuotientArray_norm_bound f _ α (div_nonneg (mul_nonneg hC hM) (monomialScale_pos T hT α).le)
  intro t
  rw [projected_lift_residual_eq (b.baseChange ℝ) w (by omega) (S t) _ (hk t), coefficients_map]
  change ‖realQuotientCoordinateMap f
    (basisGradeProjection (b.baseChange ℝ) w j (coefficients (S t) α))‖ ≤ C * M / monomialScale T α
  calc
    _ ≤ C * ‖(b.baseChange ℝ).equivFun
        (basisGradeProjection (b.baseChange ℝ) w j (coefficients (S t) α))‖ :=
      realQuotientCoordinateMap_norm_bound b f hf _
    _ ≤ C * ‖(b.baseChange ℝ).equivFun (coefficients (S t) α)‖ :=
      mul_le_mul_of_nonneg_left (basisCoordinateProjection_norm_le (b.baseChange ℝ) {n | w n = j} _) hC
    _ ≤ C * (M / monomialScale T α) := mul_le_mul_of_nonneg_left (hS t α) hC
    _ = C * M / monomialScale T α := (mul_div_assoc C M (monomialScale T α)).symm

theorem liftQuotientArray_map_neg (f : Basis ι ℚ (L ⧸ V))
    (π : (ℝ ⊗[ℚ] L) →ₗ[ℚ] (ℝ ⊗[ℚ] L))
    (R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    liftQuotientArray f (fun t => map π (-(R t))) = -liftQuotientArray f (fun t => map π (R t)) := by
  simp only [map_neg]
  exact liftQuotientArray_neg f _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FormalKernelAbsorption
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

theorem homogeneous_one_pderiv {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (P : VectorPolynomial σ ℚ L)
    (hP : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ 1 → coefficients P α = 0)
    (i : σ) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L P = monomial 0 (coefficients P (Finsupp.single i 1)) := by
  classical
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [coefficients_pderiv, coefficients_monomial]
  by_cases hα : α = 0
  · subst α
    simp only [Finsupp.zero_apply, Nat.cast_zero, zero_add, one_smul, Finsupp.single_eq_same]
  · have hp := NilpotentLieFiltration.positive_weight_of_ne_zero (fun _ : σ => 1) (by simp) hα
    have hweight : Finsupp.weight (fun _ : σ => (1 : ℕ)) (α + Finsupp.single i 1) ≠ 1 := by
      rw [map_add, Finsupp.weight_single]
      simp only [one_smul]
      omega
    rw [hP _ hweight, smul_zero, Finsupp.single_eq_of_ne hα]

end VectorPolynomial

namespace NilpotentLieBCHGroup

variable {σ K L : Type*} [AddCommGroup K] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem PolynomialDerivativeSystemMod.absorb (V : Submodule ℚ L)
    (P : PolynomialGroup σ hnil) (S R : K →+ VectorPolynomial σ ℚ L)
    (small rational : σ → VectorPolynomial σ ℚ L) (k a b : σ → K)
    (hSR : PolynomialLiftSystemMod V P S R)
    (hsystem : PolynomialDerivativeSystemMod V P small rational (fun i => S (k i))) :
    PolynomialDerivativeSystemMod V P
      (fun i => small i + S (a i)) (fun i => rational i + R (b i))
      (fun i => S (k i - a i - b i)) := by
  intro i
  have h := (coefficientSubmodule V).add_mem (hsystem i) (hSR (b i))
  change formalLogDerivative i P -
    ((small i + S (a i)) + dualAdjoint P (rational i + R (b i)) + S (k i - a i - b i)) ∈ _
  convert h using 1
  simp only [map_sub, dualAdjoint_add]
  abel

theorem formal_remove_and_absorb (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P A B : PolynomialGroup σ hnil) (hA : ∀ α, coefficients A.coord α ∈ U)
    (S R : K →+ VectorPolynomial σ ℚ L)
    (small rational : σ → VectorPolynomial σ ℚ L) (k a b : σ → K)
    (hSR : PolynomialLiftSystemMod V P S R)
    (hsystem : PolynomialDerivativeSystemMod V P small rational (fun i => S (k i))) :
    let S' := (dualAdjointAddEquiv A⁻¹).toAddMonoidHom.comp S
    let R' := (dualAdjointAddEquiv B).toAddMonoidHom.comp R
    PolynomialLiftSystemMod V (A⁻¹ * P * B⁻¹) S' R' ∧
      PolynomialDerivativeSystemMod V (A⁻¹ * P * B⁻¹)
        (fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A) + S' (a i))
        (fun i => dualAdjoint B (rational i) - formalLogDerivative i B + R' (b i))
        (fun i => S' (k i - a i - b i)) := by
  intro S' R'
  have hlifts : PolynomialLiftSystemMod V (A⁻¹ * P * B⁻¹) S' R' :=
    PolynomialLiftSystemMod.remove U V hUV P A B hA S R hSR
  have hderivative := PolynomialDerivativeSystemMod.remove U V hUV P A B hA
    small rational (fun i => S (k i)) hsystem
  exact ⟨hlifts, PolynomialDerivativeSystemMod.absorb V (A⁻¹ * P * B⁻¹) S' R'
    _ _ k a b hlifts hderivative⟩

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalHorizontalReabsorption
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hF in
theorem formal_horizontal_logDerivative (hs : 1 ≤ s) (i : σ)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ) (formalLogDerivative i P) =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord) := by
  have hP : ∀ α, coefficients P.coord α ∈ F.realification.layer 1 := by
    intro α
    rw [F.realification.one_eq_top]
    trivial
  have hD := pderiv_mem_submodule (F.realification.layer 1) P.coord hP i
  have hrem := F.realification.polynomialFiltration.dualLogDerivative_sub_tangent_mem_layer hs
    (i := 1) (j := 1) (formalPolynomialJetHom i P)
    (by rw [formalPolynomialJet_base]; exact hP)
    (by rw [formalPolynomialJet_tangent]; exact hD)
  rw [formalPolynomialJet_tangent] at hrem
  exact F.polynomial_grade_eq_of_sub_mem_next b w hF 1 _ _ hrem

include hF in
theorem formal_derivative_horizontal_balance (hs : 2 ≤ s)
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational extra)
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer 2).toSubmodule) :
    ∀ i α, coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ) (extra i)) α ∈ V := by
  intro i α
  have hP : ∀ β, coefficients P.coord β ∈ F.realification.layer 1 := by
    intro β
    rw [F.realification.one_eq_top]
    trivial
  have hY := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α)
    (F.formal_horizontal_logDerivative b w hF (by omega) i P)
  have hAd := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α)
    (F.polynomial_grade_adjoint_eq b w hF hs 1 P hP (rational i))
  simp only [coefficients_map, LinearMap.restrictScalars_apply] at hY hAd
  have herr := hV 1 _ (hsystem i α)
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply] at herr
  rw [hY, hAd] at herr
  have hS := F.realGradeProjection_mem_of_mem_sup_next b w hF V hV 1 _ (hsmall i α)
  have hR := F.realGradeProjection_mem_of_mem_sup_next b w hF V hV 1 _ (hrational i α)
  have h := V.add_mem herr (V.add_mem hS hR)
  simp only [map_sub, Finsupp.sub_apply, coefficients_map, LinearMap.restrictScalars_apply]
  convert h using 1
  abel

include hF in
theorem formal_extra_horizontal_equation (hs : 2 ≤ s)
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational extra)
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ) (extra i)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro i α
  have hbalance := F.formal_derivative_horizontal_balance b w hF hs V hV P small rational extra
    hsystem hsmall hrational i α
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).sub_mem (hextra i α) (Submodule.mem_sup_left hbalance)
  simp only [map_sub, Finsupp.sub_apply] at h ⊢
  convert h using 1
  abel

include hF in
theorem formal_lift_nonhorizontal_remainder
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    {j : ℕ} (hj : 1 ≤ j) (X : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : ℝ ⊗[ℚ] L)
    (hk : basisGradeProjection (b.baseChange ℝ) w 1 k = k)
    (hX : ∀ α, coefficients (X - monomial 0 k) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    ∀ α, coefficients (X - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ) X) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  have hproj (x : ℝ ⊗[ℚ] L) (hx : x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule) :
      basisGradeProjection (b.baseChange ℝ) w 1 x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, F.realGradeProjection_eq_zero_of_mem_next_layer b w hF 1 z
      (F.realification.antitone (by omega) hz), add_zero]
    exact Submodule.mem_sup_left (hV 1 v hv)
  intro α
  have hkα : basisGradeProjection (b.baseChange ℝ) w 1 (coefficients (monomial 0 k : VectorPolynomial σ ℚ _) α) =
      coefficients (monomial 0 k : VectorPolynomial σ ℚ _) α := by
    rw [coefficients_monomial]
    by_cases hα : α = 0
    · subst α
      simpa only [Finsupp.single_eq_same] using hk
    · rw [Finsupp.single_eq_of_ne hα, map_zero]
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).sub_mem (hX α) (hproj _ (hX α))
  simp only [map_sub, Finsupp.sub_apply, hkα] at h
  simp only [map_sub, Finsupp.sub_apply, coefficients_map, LinearMap.restrictScalars_apply]
  convert h using 1
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

section General

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem formal_logDerivative_sub_pderiv_mem_two (hs : 1 ≤ s) (i : σ)
    (A : PolynomialGroup σ F.lowerCentralSeries_eq_bot) :
    ∀ α, coefficients (formalLogDerivative i A - (MvPolynomial.pderiv i).toLinearMap.rTensor L A.coord) α ∈ F.layer 2 := by
  have hA : ∀ α, coefficients A.coord α ∈ F.layer 1 := by intro α; rw [F.one_eq_top]; trivial
  have hD := pderiv_mem_submodule (F.layer 1) A.coord hA i
  have h := F.polynomialFiltration.dualLogDerivative_sub_tangent_mem_layer hs
    (i := 1) (j := 1) (formalPolynomialJetHom i A)
    (by rw [formalPolynomialJet_base]; exact hA) (by rw [formalPolynomialJet_tangent]; exact hD)
  rw [formalPolynomialJet_tangent] at h
  exact h

theorem formal_reabsorption_preserves_layer_two (hs : 2 ≤ s) (V : Submodule ℚ L) (i : σ)
    (A B : PolynomialGroup σ F.lowerCentralSeries_eq_bot)
    (small rational left right : VectorPolynomial σ ℚ L)
    (hsmall : ∀ α, coefficients small α ∈ V ⊔ F.layer 2)
    (hrational : ∀ α, coefficients rational α ∈ V ⊔ F.layer 2)
    (hleft : ∀ α, coefficients (left - (MvPolynomial.pderiv i).toLinearMap.rTensor L A.coord) α ∈ V ⊔ F.layer 2)
    (hright : ∀ α, coefficients (right - (MvPolynomial.pderiv i).toLinearMap.rTensor L B.coord) α ∈ V ⊔ F.layer 2) :
    (∀ α, coefficients (dualAdjoint A⁻¹ (small - formalLogDerivative i A) + left) α ∈ V ⊔ F.layer 2) ∧
      ∀ α, coefficients (dualAdjoint B rational - formalLogDerivative i B + right) α ∈ V ⊔ F.layer 2 := by
  let W := coefficientSubmodule (σ := σ) (V ⊔ F.layer 2)
  have hA : ∀ α, coefficients A⁻¹.coord α ∈ F.layer 1 := by intro α; rw [F.one_eq_top]; trivial
  have hB : ∀ α, coefficients B.coord α ∈ F.layer 1 := by intro α; rw [F.one_eq_top]; trivial
  have ha := F.polynomialFiltration.adjoint_correction_sub_mem_layer hs 1 A⁻¹ hA (small - formalLogDerivative i A)
  have hb := F.polynomialFiltration.adjoint_correction_sub_mem_layer hs 1 B hB rational
  have hYa := F.formal_logDerivative_sub_pderiv_mem_two (by omega) i A
  have hYb := F.formal_logDerivative_sub_pderiv_mem_two (by omega) i B
  have haW : dualAdjoint A⁻¹ (small - formalLogDerivative i A) - (small - formalLogDerivative i A) ∈ W :=
    fun α => Submodule.mem_sup_right (ha α)
  have hbW : dualAdjoint B rational - rational ∈ W := fun α => Submodule.mem_sup_right (hb α)
  have hYaW : formalLogDerivative i A - (MvPolynomial.pderiv i).toLinearMap.rTensor L A.coord ∈ W :=
    fun α => Submodule.mem_sup_right (hYa α)
  have hYbW : formalLogDerivative i B - (MvPolynomial.pderiv i).toLinearMap.rTensor L B.coord ∈ W :=
    fun α => Submodule.mem_sup_right (hYb α)
  constructor
  · have h : dualAdjoint A⁻¹ (small - formalLogDerivative i A) + left ∈ W := by
      convert W.add_mem (W.sub_mem (W.add_mem hsmall haW) hYaW) hleft using 1
      abel
    exact h
  · have h : dualAdjoint B rational - formalLogDerivative i B + right ∈ W := by
      convert W.add_mem (W.sub_mem (W.add_mem hrational hbW) hYbW) hright using 1
      abel
    exact h

end General

variable {μ σ K L : Type*} [AddCommGroup K] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hF in
theorem formal_degree_two_reabsorption (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (I : K →+ ℝ ⊗[ℚ] L) (hI : ∀ x, basisGradeProjection (b.baseChange ℝ) w 1 (I x) = I x)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U)
    (hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ 1 → coefficients A.coord α = 0)
    (hBhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ 1 → coefficients B.coord α = 0)
    (S R : K →+ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k a c : σ → K)
    (ha : ∀ i, I (a i) = coefficients A.coord (Finsupp.single i 1))
    (hc : ∀ i, I (c i) = coefficients B.coord (Finsupp.single i 1))
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational (fun i => S (k i)))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hS : ∀ x α, coefficients (dualAdjoint A⁻¹ (S x) - monomial 0 (I x)) α ∈ V ⊔ (F.realLayer 3).toSubmodule)
    (hR : ∀ x α, coefficients (dualAdjoint B (R x) - monomial 0 (I x)) α ∈ V ⊔ (F.realLayer 3).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let S' := (dualAdjointAddEquiv A⁻¹).toAddMonoidHom.comp S
    let R' := (dualAdjointAddEquiv B).toAddMonoidHom.comp R
    let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A) + S' (a i)
    let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B + R' (c i)
    let extra' := fun i => S' (k i - a i - c i)
    PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' ∧
      PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
      (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer 2).toSubmodule ∧
        coefficients (rational' i) α ∈ V ⊔ (F.realLayer 2).toSubmodule) ∧
      ∀ i α, coefficients (extra' i - VectorPolynomial.map
        ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈ V ⊔ (F.realLayer 3).toSubmodule := by
  intro P' S' R' small' rational' extra'
  have hsystem' := formal_remove_and_absorb U (V.restrictScalars ℚ) hUV P A B hAU S R
    small rational k a c hSR hsystem
  have hWiff (d : ℕ) (x : ℝ ⊗[ℚ] L) :
      x ∈ V.restrictScalars ℚ ⊔ F.realification.layer d ↔ x ∈ V ⊔ (F.realLayer d).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer d).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have h32 : V.restrictScalars ℚ ⊔ F.realification.layer 3 ≤ V.restrictScalars ℚ ⊔ F.realification.layer 2 :=
    sup_le_sup_left (F.realification.antitone (by decide : 2 ≤ 3)) _
  have hlow (i : σ) := F.realification.formal_reabsorption_preserves_layer_two hs (V.restrictScalars ℚ) i A B
    (small i) (rational i) (S' (a i)) (R' (c i))
    (fun α => (hWiff 2 _).mpr (hsmall i α)) (fun α => (hWiff 2 _).mpr (hrational i α))
    (fun α => by
      rw [homogeneous_one_pderiv A.coord hAhom i, ← ha i]
      exact h32 ((hWiff 3 _).mpr (hS (a i) α)))
    (fun α => by
      rw [homogeneous_one_pderiv B.coord hBhom i, ← hc i]
      exact h32 ((hWiff 3 _).mpr (hR (c i) α)))
  have hsmall' : ∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer 2).toSubmodule :=
    fun i α => (hWiff 2 _).mp ((hlow i).1 α)
  have hrational' : ∀ i α, coefficients (rational' i) α ∈ V ⊔ (F.realLayer 2).toSubmodule :=
    fun i α => (hWiff 2 _).mp ((hlow i).2 α)
  refine ⟨hsystem'.1, hsystem'.2, (fun i α => ⟨hsmall' i α, hrational' i α⟩), ?_⟩
  apply F.formal_extra_horizontal_equation b w hF hs V hV 2 P' small' rational' extra'
    hsystem'.2 hsmall' hrational'
  intro i
  exact F.formal_lift_nonhorizontal_remainder b w hF V hV (by decide : 1 ≤ 2)
    (extra' i) (I (k i - a i - c i)) (hI _) (hS _)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.UniformControlledBracketStage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct Matrix

variable {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {E V : Submodule ℚ L}

include hlayers in
theorem exists_controlled_bracket_polynomial_step
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (hgraded : BasisHomogeneousBrackets (b.baseChange ℝ) w)
    {d H J l : ℕ} (hd : 0 < d)
    (hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w d x = x)
    (hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P Pd : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hPU : ∀ α, coefficients P α ∈ U)
    (hPgraded : P ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (hPd : Pd = map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P)
    (hPdE : ∀ α, coefficients Pd α ∈ E.baseChange ℝ)
    (small rational : VectorPolynomial σ ℚ (κ × ι → ℝ))
    (hsmallhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients small α = 0)
    (hrationalhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients rational α = 0)
    (hsmall : ∀ α, ‖coefficients small α‖ ≤ Real.exp p / monomialScale T α)
    (hrational : ∀ α, coefficients rational α ∈ realDenominatorGrid l)
    (heq : ∀ α, realBracketSystem f k (coefficients Pd α) =
      coefficients small α + coefficients rational α) :
    ∃ (m : ℕ) (A B P' : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map ((realBracketSystem f k).restrictScalars ℚ) A = small ∧
      map ((realBracketSystem f k).restrictScalars ℚ) B = rational ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients A α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      P' = bchRemove s A P B ∧ lieBCH s (lieBCH s A P') B = P ∧
      coefficients P' 0 = coefficients P 0 ∧
      P' ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
      (∀ α, coefficients P' α ∈ U) ∧
      (∀ α t, ⁅coefficients (map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P') α,
        (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ) ∧
      ∀ r < d, map ((basisGradeProjection (b.baseChange ℝ) w r).restrictScalars ℚ) P' =
        map ((basisGradeProjection (b.baseChange ℝ) w r).restrictScalars ℚ) P := by
  obtain ⟨Q, hQ, hQzero⟩ := exists_subspace_coordinate_polynomial e Pd hPdE
  have hPd0 : coefficients Pd 0 = 0 := by
    rw [hPd]
    exact gradedPolynomialSubmodule_projection_homogeneous (b.baseChange ℝ) w (fun _ => 1)
      P hPgraded d 0 (by simpa using Nat.ne_of_lt hd)
  have hcoeff (α : σ →₀ ℕ) : bracketSystemLift e (coefficients Q α) = coefficients Pd α := by
    have h := congrArg (fun p => coefficients p α) hQ
    simpa only [coefficients_map, LinearMap.restrictScalars_apply] using h
  have hsmall0 : coefficients small 0 = 0 := hsmallhom 0 (by simpa using Nat.ne_of_lt hd)
  have hrational0 : coefficients rational 0 = 0 := hrationalhom 0 (by simpa using Nat.ne_of_lt hd)
  have h := exists_ambient_bracket_correction_polynomials b e f k hH hl hA he hp hrows hcols hHp hlp
    T hT Q small rational (hQzero 0 hPd0) hsmall0 hrational0 hsmall hrational
    (fun α => by rw [hcoeff]; exact heq α)
  obtain ⟨m, A, B, hm, hmp, hAQ, hBQ, hAB, hAzero, hBzero, hAnorm, hBgrid, hres⟩ := h
  have hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients A α = 0 :=
    fun α hα => hAzero α (hsmallhom α hα)
  have hBhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients B α = 0 :=
    fun α hα => hBzero α (hrationalhom α hα)
  have hgrades := F.polynomial_bchRemove_grades b w hlayers (E.baseChange ℝ) d hE A P B
    (fun α => (hAB α).1) (fun α => (hAB α).2)
  have hAgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1)
    d A hAhom (fun α => hE _ (hAB α).1)
  have hBgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1)
    d B hBhom (fun α => hE _ (hAB α).2)
  refine ⟨m, A, B, bchRemove s A P B, hm, hmp, hAQ, hBQ, hAB, hAhom, hBhom, hAnorm, hBgrid,
    rfl, bchRemove_factorization F.realification.lowerCentralSeries_eq_bot A P B,
    bchRemove_constant F.realification.lowerCentralSeries_eq_bot A P B
      (hAzero 0 hsmall0) (hBzero 0 hrational0),
    bchRemove_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w hgraded (fun _ => 1) s A P B
      hAgraded hPgraded hBgraded,
    bchRemove_coefficients_mem U s A P B (fun α => hEU _ (hAB α).1) hPU
      (fun α => hEU _ (hAB α).2), ?_, hgrades.2⟩
  intro α t
  rw [hgrades.1, ← hPd]
  simpa only [hQ] using hres α t

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_bracket_induction_step (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (k : κ → ℝ ⊗[ℚ] L) (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 (k t) = k t)
    {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hAU : ∀ α, coefficients A.coord α ∈ U)
    (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) =
      coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) =
      coefficients B.coord α)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hSR : PolynomialLiftSystem P S R)
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), k t⁆ ∈ V)
    (hleft : ∀ t α, coefficients (S t - monomial 0 (k t) - ⁅A.coord, monomial 0 (k t)⁆) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hright : ∀ t α, coefficients (R t - monomial 0 (k t) + ⁅B.coord, monomial 0 (k t)⁆) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let S' := fun t => dualAdjoint A⁻¹ (S t)
    let R' := fun t => dualAdjoint B (R t)
    A * P' * B = P ∧ (∀ α, coefficients P'.coord α ∈ U) ∧
      (∀ d < j - 1,
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
      (∀ d < j, ∀ t α,
        ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), k t⁆ ∈ V) ∧
      PolynomialLiftSystem P' S' R' ∧
      ∀ t α,
        coefficients (S' t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        coefficients (R' t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        ⁅coefficients P'.coord α, k t⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro P' S' R'
  let Vq := V.restrictScalars ℚ
  let p := VectorPolynomial.map
    ((basisGradeProjection (b.baseChange ℝ) w (j - 1)).restrictScalars ℚ) P.coord
  have hW (d : ℕ) (x : ℝ ⊗[ℚ] L) :
      x ∈ Vq ⊔ F.realification.layer d ↔ x ∈ V ⊔ (F.realLayer d).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer d).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have hp : p ∈ F.realification.polynomialFiltration.layer (j - 1) := by
    intro α
    rw [coefficients_map]
    exact F.realGradeProjection_mem_layer b w hlayers (j - 1) _
  have ha : A.coord ∈ F.realification.polynomialFiltration.layer (j - 1) := by
    intro α
    rw [← hA α]
    exact F.realGradeProjection_mem_layer b w hlayers (j - 1) _
  have hb : B.coord ∈ F.realification.polynomialFiltration.layer (j - 1) := by
    intro α
    rw [← hB α]
    exact F.realGradeProjection_mem_layer b w hlayers (j - 1) _
  have hkl (t : κ) : k t ∈ F.realification.layer 1 := by
    rw [F.realification.one_eq_top]
    trivial
  have hstep : j - 1 + 2 = j + 1 := by omega
  have hrem (t : κ) (α : σ →₀ ℕ) :
      coefficients (⁅P.coord - p, monomial (R := ℚ) 0 (k t)⁆ :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    have h := F.real_current_bracket_remainder b w hlayers V (j - 1)
      (coefficients P.coord α) (k t) (hkl t) (fun d hd => hlower d hd t α)
    rw [hstep] at h
    simpa only [p, coefficients_lie_constant, map_sub, Finsupp.sub_apply, coefficients_map,
      LinearMap.restrictScalars_apply] using h
  have hnorm := F.realification.polynomialFiltration.current_layer_normalization hs
    (coefficientLieSubalgebra U) (coefficientSubmodule Vq)
    (fun X hX Y hY => coefficientSubmodule_invariant U Vq hUV X Y hX hY)
    hj P A B hPU hAU hBU ha hb S R (fun t => monomial 0 (k t)) p hp hSR
    (fun t => (mem_coefficient_sup_polynomialLayer F.realification Vq j _).mpr
      (fun α => (hW j _).mpr (hR t α)))
    (fun t => (mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mpr
      (fun α => (hW (j + 1) _).mpr (hrem t α)))
    (fun t => (mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mpr
      (fun α => (hW (j + 1) _).mpr (hleft t α)))
    (fun t => (mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mpr
      (fun α => (hW (j + 1) _).mpr (hright t α)))
  obtain ⟨hprod, hP'U, _, _, hS'R', hcurrent⟩ := hnorm
  let E := LinearMap.ker (basisGradeProjection (b.baseChange ℝ) w (j - 1) - LinearMap.id)
  have hE : ∀ x ∈ E, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x := by
    intro x hx
    exact sub_eq_zero.mp hx
  have haE : ∀ α, coefficients A.coord α ∈ E := fun α => sub_eq_zero.mpr (hA α)
  have hbE : ∀ α, coefficients B.coord α ∈ E := fun α => sub_eq_zero.mpr (hB α)
  have hgrades := F.polynomial_bchRemove_grades b w hlayers E (j - 1) hE A.coord P.coord B.coord haE hbE
  have hgrade : VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w (j - 1)).restrictScalars ℚ) P'.coord =
      p - A.coord - B.coord := hgrades.1
  have hcur (t : κ) (α : σ →₀ ℕ) :
      ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P'.coord α), k t⁆ ∈ V := by
    apply F.real_mem_of_homogeneous_mem_sup_next b w hlayers V hV j
    · have h := (hgraded.baseChange b w).projection_lie (b.baseChange ℝ) w
        (basisCoordinateProjection_idempotent (b.baseChange ℝ) {i | w i = j - 1}
          (coefficients P'.coord α)) (hk t)
      simp only [Nat.sub_add_cancel (by omega : 1 ≤ j)] at h
      exact h
    · have h := (hW (j + 1) _).mp
        ((mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mp
          (hcurrent t).2.2 α)
      rw [← hgrade, coefficients_lie_constant, coefficients_map] at h
      exact h
  have hall (d : ℕ) (hd : d < j) (t : κ) (α : σ →₀ ℕ) :
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), k t⁆ ∈ V := by
    rcases lt_or_eq_of_le (show d ≤ j - 1 by omega) with hlt | rfl
    · have h := congrArg (fun Q => coefficients Q α) (hgrades.2 d hlt)
      simp only [coefficients_map, LinearMap.restrictScalars_apply] at h
      have he : basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) =
          basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) := h
      rw [he]
      exact hlower d hlt t α
    · exact hcur t α
  refine ⟨hprod, hP'U, hgrades.2, hall, hS'R', fun t α => ⟨?_, ?_, ?_⟩⟩
  · exact (hW (j + 1) _).mp
      ((mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mp (hcurrent t).1 α)
  · exact (hW (j + 1) _).mp
      ((mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mp (hcurrent t).2.1 α)
  · have h := F.real_current_bracket_remainder b w hlayers V (j - 1)
      (coefficients P'.coord α) (k t) (hkl t) (fun d hd => hall d (by omega) t α)
    rw [hstep] at h
    have ht := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem h
      (Submodule.mem_sup_left (hcur t α))
    simpa only [sub_lie, sub_add_cancel] using ht

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {μ ι κ σ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {V : Submodule ℚ L}

include hlayers in
theorem bracket_array_matching_remainder
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) (j : ℕ)
    (X : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (A : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hX : ∀ t α, coefficients (X t) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hA : map ((realBracketSystem f k).restrictScalars ℚ) A =
      liftQuotientArray f (fun t =>
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (X t))) :
    ∀ t α, coefficients (X t - ⁅A, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) α ∈
      V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  have hmatch := bracket_system_matches_lift_array f k A _ hA
  intro t
  exact F.polynomial_lift_matching_remainder b w hlayers (V.baseChange ℝ) hV j
    (X t) _ (hX t) (hmatch t)

include hlayers in
theorem bracket_arrays_match_lifts
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) (j : ℕ)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ t α, coefficients (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hR : ∀ t α, coefficients (R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hA : map ((realBracketSystem f k).restrictScalars ℚ) A =
      liftQuotientArray f (fun t => map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))
    (hB : map ((realBracketSystem f k).restrictScalars ℚ) B =
      liftQuotientArray f (fun t => map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))) :
    (∀ t α, coefficients (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t) -
      ⁅A, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
    ∀ t α, coefficients (R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t) +
      ⁅B, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  refine ⟨F.bracket_array_matching_remainder b w hlayers hV f k j _ A hS hA, ?_⟩
  have hneg : ∀ t α, coefficients (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule := by
    intro t α
    rw [map_neg, Finsupp.neg_apply]
    exact Submodule.neg_mem _ (hR t α)
  have hmatch := F.bracket_array_matching_remainder b w hlayers hV f k j _ B hneg hB
  intro t α
  have he : R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t) + ⁅B, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆ =
      -(-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) - ⁅B, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) := by abel
  rw [he, map_neg, Finsupp.neg_apply]
  exact Submodule.neg_mem _ (hmatch t α)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_current_bracket_equation (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (k : κ → ℝ ⊗[ℚ] L) (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 (k t) = k t)
    {j : ℕ} (hj : 2 ≤ j) (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hSR : PolynomialLiftSystem P S R)
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), k t⁆ ∈ V) :
    ∀ t α, ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ -
      (basisGradeProjection (b.baseChange ℝ) w j (coefficients (S t) α) -
        basisGradeProjection (b.baseChange ℝ) w j (coefficients (R t) α)) ∈ V := by
  let Vq := V.restrictScalars ℚ
  let p := VectorPolynomial.map
    ((basisGradeProjection (b.baseChange ℝ) w (j - 1)).restrictScalars ℚ) P.coord
  have hW (d : ℕ) (x : ℝ ⊗[ℚ] L) :
      x ∈ Vq ⊔ F.realification.layer d ↔ x ∈ V ⊔ (F.realLayer d).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer d).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have hp : p ∈ F.realification.polynomialFiltration.layer (j - 1) := by
    intro α
    rw [coefficients_map]
    exact F.realGradeProjection_mem_layer b w hlayers (j - 1) _
  have hk1 (t : κ) : k t ∈ F.realification.layer 1 := by
    rw [F.realification.one_eq_top]
    trivial
  have hstep : j - 1 + 2 = j + 1 := by omega
  intro t α
  have hrem : (⁅P.coord - p, monomial (R := ℚ) 0 (k t)⁆ : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
      coefficientSubmodule Vq ⊔ F.realification.polynomialFiltration.layer (j + 1) := by
    apply (mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mpr
    intro β
    apply (hW (j + 1) _).mpr
    have h := F.real_current_bracket_remainder b w hlayers V (j - 1)
      (coefficients P.coord β) (k t) (hk1 t) (fun d hd => hlower d hd t β)
    rw [hstep] at h
    simpa only [p, coefficients_lie_constant, map_sub, Finsupp.sub_apply,
      coefficients_map, LinearMap.restrictScalars_apply] using h
  have hconst : monomial (R := ℚ) (0 : σ →₀ ℕ) (k t) ∈ F.realification.polynomialFiltration.layer 1 :=
    F.realification.monomial_mem_polynomialLayer 1 0 (hk1 t)
  have h := F.realification.polynomialFiltration.adjoint_current_layer_relation
    (coefficientLieSubalgebra U) (coefficientSubmodule Vq)
    (fun X hX Y hY => coefficientSubmodule_invariant U Vq hUV X Y hX hY)
    hs (by omega) P hPU (R t) (monomial 0 (k t)) p hp hconst
    ((mem_coefficient_sup_polynomialLayer F.realification Vq j _).mpr
      (fun β => (hW j _).mpr (hR t β))) hrem
  rw [← hSR t] at h
  have hc := (hW (j + 1) _).mp
    ((mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mp h α)
  have hscalar : ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ -
      (coefficients (S t) α - coefficients (R t) α) ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    simpa only [p, map_sub, Finsupp.sub_apply, coefficients_lie_constant,
      coefficients_map, LinearMap.restrictScalars_apply] using hc
  have hhom : basisGradeProjection (b.baseChange ℝ) w j
      ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ =
      ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ := by
    have hh := (hgraded.baseChange b w).projection_lie (b.baseChange ℝ) w
      (basisCoordinateProjection_idempotent (b.baseChange ℝ) {i | w i = j - 1}
        (coefficients P.coord α)) (hk t)
    simp only [Nat.sub_add_cancel (by omega : 1 ≤ j)] at hh
    exact hh
  have hproj := F.realGradeProjection_mem_of_mem_sup_next b w hlayers V hV j _ hscalar
  simpa only [map_sub, hhom] using hproj

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_current_bracket_equation_mod (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (k : κ → ℝ ⊗[ℚ] L) (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 (k t) = k t)
    {j : ℕ} (hj : 2 ≤ j) (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), k t⁆ ∈ V) :
    ∀ t α, ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ -
      (basisGradeProjection (b.baseChange ℝ) w j (coefficients (S t) α) -
        basisGradeProjection (b.baseChange ℝ) w j (coefficients (R t) α)) ∈ V := by
  obtain ⟨S₀, hS₀, herror⟩ := PolynomialLiftSystemMod.exact_left (V.restrictScalars ℚ) P S R hSR
  have hcurrent := F.formal_current_bracket_equation b w hlayers hgraded hs U V hUV hV
    k hk hj P hPU S₀ R hS₀ hR hlower
  intro t α
  have he := hV j (coefficients (S t - S₀ t) α) (herror t α)
  simp only [map_sub, Finsupp.sub_apply] at he
  have h := V.sub_mem (hcurrent t α) he
  convert h using 1
  abel

include hlayers in
theorem formal_bracket_induction_step_mod (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (k : κ → ℝ ⊗[ℚ] L) (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 (k t) = k t)
    {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) = coefficients B.coord α)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), k t⁆ ∈ V)
    (hleft : ∀ t α, coefficients (S t - monomial 0 (k t) - ⁅A.coord, monomial 0 (k t)⁆) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hright : ∀ t α, coefficients (R t - monomial 0 (k t) + ⁅B.coord, monomial 0 (k t)⁆) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let S' := fun t => dualAdjoint A⁻¹ (S t)
    let R' := fun t => dualAdjoint B (R t)
    A * P' * B = P ∧ (∀ α, coefficients P'.coord α ∈ U) ∧
      (∀ d < j - 1,
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
      (∀ d < j, ∀ t α,
        ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), k t⁆ ∈ V) ∧
      PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' ∧
      ∀ t α,
        coefficients (S' t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        coefficients (R' t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        ⁅coefficients P'.coord α, k t⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro P' S' R'
  obtain ⟨S₀, hS₀, herror⟩ := PolynomialLiftSystemMod.exact_left (V.restrictScalars ℚ) P S R hSR
  have hleft₀ (t : κ) (α : σ →₀ ℕ) :
      coefficients (S₀ t - monomial 0 (k t) - ⁅A.coord, monomial 0 (k t)⁆) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).sub_mem
      (hleft t α) (Submodule.mem_sup_left (herror t α))
    simp only [map_sub, Finsupp.sub_apply] at h ⊢
    convert h using 1
    abel
  have hstep := F.formal_bracket_induction_step b w hlayers hgraded hs U V hUV hV k hk hj
    P A B hPU hAU hBU hA hB S₀ R hS₀ hR hlower hleft₀ hright
  obtain ⟨hprod, hU, hbelow, hbracket, _, hnext⟩ := hstep
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ U := (coefficientLieSubalgebra U).neg_mem hAU
  refine ⟨hprod, hU, hbelow, hbracket,
    PolynomialLiftSystemMod.remove U (V.restrictScalars ℚ) hUV P A B hAU S R hSR,
    fun t α => ⟨?_, (hnext t α).2.1, (hnext t α).2.2⟩⟩
  have he := dualAdjoint_mem_coefficientSubmodule U (V.restrictScalars ℚ) hUV A⁻¹
    (S t - S₀ t) hAi (herror t)
  have heq : dualAdjoint A⁻¹ (S t) - monomial 0 (k t) =
      dualAdjoint A⁻¹ (S t - S₀ t) + (dualAdjoint A⁻¹ (S₀ t) - monomial 0 (k t)) := by
    rw [dualAdjoint_sub]
    abel
  change coefficients (dualAdjoint A⁻¹ (S t) - monomial 0 (k t)) α ∈ _
  rw [heq, map_add, Finsupp.add_apply]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (he α)) (hnext t α).1

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FirstCoefficientPolynomialDerivative
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem adaptedShiftedGradedPolynomial_directionalDerivative (h : σ → ℚ) (k : ℕ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.adaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) (k + 1)
        (F.adaptedDirectionalDerivative h p) =
      directionalDerivative h (F.adaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) k p) := by
  rw [F.adaptedShiftedGradedPolynomial_apply, F.adaptedDirectionalDerivative_coe,
    F.adaptedShiftedGradedPolynomial_apply]
  exact F.shiftedGradedPolynomial_directionalDerivative b ω hF h k p.val

end Erdos3.NilpotentLieFiltration

end

end OAI
end


