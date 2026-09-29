-- Prove2me | solution 1 for AutomorphicForm.exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1239f6fa-4bda-57ed-a203-0c83e1c90cfe

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_sum_mult_mul_log_one_add_norm_archEval_archIdent_smul_inv_eq_and_sum_mult_eq_finrank_mul
import Theorems.Thm_AutomorphicForm_exists_linearMap_resolvent_integral_comp_sigmaTensor_sub_mul_eq_integral_mul_comp_smul
import Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace A5RA

theorem isUnit_infiniteAdeleRing_iff (K : Type) [Field K] [NumberField K] (x : InfiniteAdeleRing K) :
    IsUnit x ↔ ∀ v : InfinitePlace K, x v ≠ 0 := by
  rw [show IsUnit x ↔ ∀ v : InfinitePlace K, IsUnit (x v) from Pi.isUnit_iff]
  exact forall_congr' fun v => isUnit_iff_ne_zero

noncomputable def iotaL (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    (L ⊗[K] InfiniteAdeleRing K) ≃ₜ NumberField.mixedEmbedding.mixedSpace L :=
  (AutomorphicForm.archIdentHomeomorph K L).trans
    ((NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace L).homeomorph _)

theorem iotaL_apply (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (y : L ⊗[K] InfiniteAdeleRing K) :
    iotaL K L y = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y) := rfl

theorem continuous_archEval_archIdent (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w' : InfinitePlace L) :
    Continuous fun y : L ⊗[K] InfiniteAdeleRing K => NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L y) := by
  have h1 : Continuous (AutomorphicForm.archIdent K L) := by
    have := (AutomorphicForm.archIdentHomeomorph K L).continuous
    exact this
  exact (continuous_apply w').comp h1

end A5RA

open scoped Classical in
open A5RA in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (w : NumberField.InfinitePlace K)
    (r : L ⊗[K] InfiniteAdeleRing K) (c : (InfiniteAdeleRing K)ˣ)
    (hc : (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) r)
    (Ψ : NumberField.mixedEmbedding.mixedSpace L → ℂ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ M : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K), Continuous M ∧
      (∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y = (c : InfiniteAdeleRing K) • y) ∧
      (∀ y, M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = (c : InfiniteAdeleRing K) • y) ∧
      Integrable (fun y : L ⊗[K] InfiniteAdeleRing K =>
        Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y))) * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
            (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (y))‖ ^ 2)) : ℝ) : ℂ)) lam ∧
      Integrable (fun y : L ⊗[K] InfiniteAdeleRing K => Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y)))) lam ∧
      (∀ w' : NumberField.InfinitePlace L, Integrable (fun y : L ⊗[K] InfiniteAdeleRing K =>
        Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))) *
          (Real.log (‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ ^ 2 +
            ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (M y))‖ ^ 2) : ℂ)) lam) ∧
      ((∏ v : NumberField.InfinitePlace K,
          ‖NumberField.AdelicLevel.archEval K v (c : InfiniteAdeleRing K)‖ ^ v.mult : ℝ) : ℂ) *
        ∫ y, Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y))) * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
            (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (y))‖ ^ 2)) : ℝ) : ℂ) ∂lam =
      -2 * (Module.finrank K L : ℂ) *
          (((w.mult : ℝ) * Real.log ‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ : ℝ) : ℂ) *
          ∫ y, Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))) ∂lam +
        ∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
          (w'.mult : ℂ) * ∫ y, Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))) *
            (Real.log (‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (M y))‖ ^ 2) : ℂ) ∂lam := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  obtain ⟨M, hMc, hM1, hM2, hInt, hId⟩ :=
    AutomorphicForm.exists_linearMap_resolvent_integral_comp_sigmaTensor_sub_mul_eq_integral_mul_comp_smul
      K L σ hgen hdeg lam r c hc

  set f : (L ⊗[K] InfiniteAdeleRing K) → ℂ := fun y =>
    Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)) with hf
  set ω : (L ⊗[K] InfiniteAdeleRing K) → ℝ := fun y =>
    ∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
      (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L y)‖ ^ 2) with hω
  set cw : ℝ := ‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ with hcw
  set Aw : NumberField.InfinitePlace L → (L ⊗[K] InfiniteAdeleRing K) → ℝ := fun w' y =>
    Real.log (cw ^ 2 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (M y))‖ ^ 2) with hAw

  have hfc : Continuous f := hΨ.comp (iotaL K L).continuous
  have hfs : HasCompactSupport f := by
    rw [show f = Ψ ∘ (iotaL K L) from rfl]
    exact hΨc.comp_homeomorph _
  have hωc : Continuous ω := by
    refine continuous_finsetSum _ fun w' _ => continuous_const.mul ?_
    exact ((continuous_const.add ((continuous_archEval_archIdent K L w').norm.pow 2))).log fun y =>
      (add_pos_of_pos_of_nonneg one_pos (by first | positivity | exact pow_nonneg (norm_nonneg _) 2 | exact sq_nonneg _)).ne'
  have hcw0 : 0 < cw := by
    rw [hcw]
    exact norm_pos_iff.mpr ((isUnit_infiniteAdeleRing_iff K _).mp (Units.isUnit c) w)
  have hAwc : ∀ w', Continuous (Aw w') := by
    intro w'
    exact (continuous_const.add (((continuous_archEval_archIdent K L w').comp hMc).norm.pow 2)).log fun y =>
      (add_pos_of_pos_of_nonneg (pow_pos hcw0 2) (by first | positivity | exact pow_nonneg (norm_nonneg _) 2 | exact sq_nonneg _)).ne'

  have hi2 : Integrable f lam := hfc.integrable_of_hasCompactSupport hfs
  have hi3 : ∀ w', Integrable (fun y => f y * (Aw w' y : ℂ)) lam := fun w' =>
    (hfc.mul (Complex.continuous_ofReal.comp (hAwc w'))).integrable_of_hasCompactSupport (hfs.mul_right)
  have hinv : ∀ y, (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) •
      M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = y := by
    intro y; rw [hM2, smul_smul, Units.inv_mul, one_smul]
  have hi1 : Integrable (fun y => f (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) * (ω y : ℂ)) lam := by
    have hg : Integrable (fun z => f z * (ω ((((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) • M z) : ℂ)) lam :=
      (hfc.mul (Complex.continuous_ofReal.comp (hωc.comp ((continuous_const_smul _).comp hMc)))).integrable_of_hasCompactSupport
        hfs.mul_right
    have := (hInt (fun z => f z * (ω ((((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) • M z) : ℂ))).mpr hg
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hinv]
  refine ⟨M, hMc, hM1, hM2, hi1, hi2, hi3, ?_⟩

  have hR1 := fun x => (AutomorphicForm.sum_mult_mul_log_one_add_norm_archEval_archIdent_smul_inv_eq_and_sum_mult_eq_finrank_mul
    K L w c x).2
  have step1 := hId f (fun y => (ω y : ℂ))
  rw [step1]

  have hpt : ∀ y, (ω ((((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) • M y) : ℂ) =
      ∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
        ((w'.mult : ℝ) : ℂ) * ((Aw w' y : ℂ) - 2 * (Real.log cw : ℂ)) := by
    intro y
    obtain ⟨hsum, -⟩ := hR1 (M y)
    simp only [hω, hAw, hcw]
    rw [hsum]
    push_cast
    rfl
  have hcard : ((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
      (w'.mult : ℝ) : ℝ) : ℂ) = (Module.finrank K L : ℂ) * (w.mult : ℂ) := by
    obtain ⟨-, hmult⟩ := hR1 0
    have : (∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
      (w'.mult : ℝ)) = ((Module.finrank K L * w.mult : ℕ) : ℝ) := by
      rw [← hmult]; push_cast; rfl
    rw [this]; push_cast; ring
  simp_rw [hpt]

  have hterm : ∀ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
      Integrable (fun y => f y * (((w'.mult : ℝ) : ℂ) * ((Aw w' y : ℂ) - 2 * (Real.log cw : ℂ)))) lam := by
    intro w' _
    have : (fun y => f y * (((w'.mult : ℝ) : ℂ) * ((Aw w' y : ℂ) - 2 * (Real.log cw : ℂ)))) =
        fun y => ((w'.mult : ℝ) : ℂ) * (f y * (Aw w' y : ℂ)) - ((w'.mult : ℝ) : ℂ) * (2 * (Real.log cw : ℂ)) * f y := by
      funext y; ring
    rw [this]
    exact ((hi3 w').const_mul _).sub (hi2.const_mul _)
  rw [show (fun y => f y * ∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
        ((w'.mult : ℝ) : ℂ) * ((Aw w' y : ℂ) - 2 * (Real.log cw : ℂ))) =
      fun y => ∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
        f y * (((w'.mult : ℝ) : ℂ) * ((Aw w' y : ℂ) - 2 * (Real.log cw : ℂ))) from funext fun y => Finset.mul_sum _ _ _]
  rw [integral_finset_sum _ hterm]
  have hsplit : ∀ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
      ∫ y, f y * (((w'.mult : ℝ) : ℂ) * ((Aw w' y : ℂ) - 2 * (Real.log cw : ℂ))) ∂lam =
        ((w'.mult : ℝ) : ℂ) * ∫ y, f y * (Aw w' y : ℂ) ∂lam - ((w'.mult : ℝ) : ℂ) * (2 * (Real.log cw : ℂ)) * ∫ y, f y ∂lam := by
    intro w' hw'
    have : (fun y => f y * (((w'.mult : ℝ) : ℂ) * ((Aw w' y : ℂ) - 2 * (Real.log cw : ℂ)))) =
        fun y => ((w'.mult : ℝ) : ℂ) * (f y * (Aw w' y : ℂ)) - ((w'.mult : ℝ) : ℂ) * (2 * (Real.log cw : ℂ)) * f y := by
      funext y; ring
    rw [this, integral_sub ((hi3 w').const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [show (∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
      ((w'.mult : ℝ) : ℂ)) = (Module.finrank K L : ℂ) * (w.mult : ℂ) from by rw [← hcard]; push_cast; rfl]
  simp only [hf, hAw, hcw]
  push_cast
  ring

end S_AutomorphicForm_exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum
end P2MW
export P2MW.S_AutomorphicForm_exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum (solution)
