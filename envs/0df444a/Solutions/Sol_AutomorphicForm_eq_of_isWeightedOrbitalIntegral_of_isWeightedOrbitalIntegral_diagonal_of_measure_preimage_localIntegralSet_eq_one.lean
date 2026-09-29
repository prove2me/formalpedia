-- Prove2me | solution 1 for AutomorphicForm.eq_of_isWeightedOrbitalIntegral_of_isWeightedOrbitalIntegral_diagonal_of_measure_preimage_localIntegralSet_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b4a7e43d-37e1-5942-8224-e6b51cc2c92f

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_IsWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq
import Theorems.Thm_AutomorphicForm_weight_localCentralizer_mul_and_semiLocalWeight_twistedCentralizer_mul_of_diagonal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_eq_of_isWeightedOrbitalIntegral_of_isWeightedOrbitalIntegral_diagonal_of_measure_preimage_localIntegralSet_eq_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped NNReal ENNReal

namespace WUFin

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem isClosed_localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    IsClosed (AutomorphicForm.localCentralizer K v γ : Set (GL (Fin 2) (v.adicCompletion K))) := by
  have h : (AutomorphicForm.localCentralizer K v γ : Set (GL (Fin 2) (v.adicCompletion K))) = {x | γ * x = x * γ} := by
    ext x
    simp [Subgroup.mem_centralizer_iff]
  rw [h]
  exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

theorem secondCountableTopology_localGL : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem continuous_weight {F : Type*} [NormedField F] :
    Continuous (AutomorphicForm.LocalWeight.weight : GL (Fin 2) F → ℝ) := by
  have hc : Continuous fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F) := Units.continuous_val
  have he : ∀ i j : Fin 2, Continuous fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F) i j :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp hc)
  have hdet : Continuous fun x : GL (Fin 2) F => ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ := (hc.matrix_det).norm
  have htop : Continuous fun x : GL (Fin 2) F =>
      max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ :=
    ((he 0 0).norm).max ((he 0 1).norm)
  have hbot : Continuous fun x : GL (Fin 2) F => NumberField.AdelicHeight.rowMaxNorm (x : Matrix (Fin 2) (Fin 2) F) :=
    ((he 1 0).norm).max ((he 1 1).norm)
  have hdet0 : ∀ x : GL (Fin 2) F, ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ ≠ 0 := fun x =>
    (norm_pos_iff.mpr (Matrix.isUnits_det_units x).ne_zero).ne'
  have htop0 : ∀ x : GL (Fin 2) F,
      max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ ≠ 0 := by
    intro x h0
    have h00 : (x : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 :=
      norm_eq_zero.mp (le_antisymm (le_trans (le_max_left _ _) h0.le) (norm_nonneg _))
    have h01 : (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 :=
      norm_eq_zero.mp (le_antisymm (le_trans (le_max_right _ _) h0.le) (norm_nonneg _))
    have hd : (x : Matrix (Fin 2) (Fin 2) F).det = 0 := by
      rw [Matrix.det_fin_two, h00, h01, zero_mul, zero_mul, sub_zero]
    exact (Matrix.isUnits_det_units x).ne_zero hd
  unfold AutomorphicForm.LocalWeight.weight
  exact continuous_const.mul
    (((htop.mul hbot).div hdet hdet0).log fun x =>
      div_ne_zero (mul_ne_zero (htop0 x) (NumberField.AdelicHeight.rowMaxNorm_pos x).ne') (hdet0 x))

end WUFin

open WUFin in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (hγ₀₁ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0)
    (hγ₁₀ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)
    (τ₁ τ₂ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (h₁ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ₁)
    (h₂ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ₂)
    (h₁1 : τ₁ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (h₂1 : τ₂ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (J₁ J₂ : ℂ) (hJ₁ : AutomorphicForm.IsWeightedOrbitalIntegral K v γ τ₁ f J₁)
    (hJ₂ : AutomorphicForm.IsWeightedOrbitalIntegral K v γ τ₂ f J₂) : J₁ = J₂ := by
  letI : MeasurableSpace (AutomorphicForm.localCentralizer K v γ) := AutomorphicForm.localCentralizerBorel K v γ
  haveI : BorelSpace (AutomorphicForm.localCentralizer K v γ) := ⟨rfl⟩
  haveI := AutomorphicForm.locallyCompactSpace_localGL K v
  haveI := secondCountableTopology_localGL K v
  haveI : LocallyCompactSpace (AutomorphicForm.localCentralizer K v γ) :=
    (isClosed_localCentralizer K v γ).locallyCompactSpace
  haveI : SecondCountableTopology (AutomorphicForm.localCentralizer K v γ) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI := h₁
  haveI := h₂
  have heq : τ₁ = τ₂ := by
    have h := Measure.isMulLeftInvariant_eq_smul τ₁ τ₂
    have hc : Measure.haarScalarFactor τ₁ τ₂ = 1 := by
      have h' := congrArg (fun μ : Measure (AutomorphicForm.localCentralizer K v γ) =>
        μ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v)) h
      simp only [Measure.smul_apply, h₁1, h₂1, ENNReal.smul_def, smul_eq_mul, mul_one] at h'
      exact_mod_cast h'.symm
    rw [h, hc, one_smul]
  subst heq

  have hwt := (AutomorphicForm.weight_localCentralizer_mul_and_semiLocalWeight_twistedCentralizer_mul_of_diagonal K K (AlgEquiv.refl : K ≃ₐ[K] K) v).1 γ hγ₁₀ hγ₀₁ hγ

  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.glBorelOf (v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := ⟨rfl⟩
  have hfc : Continuous f := hf.1.continuous
  have hfm : Measurable f := hfc.measurable
  have hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C := hfc.bounded_above_of_compact_support hf.2
  exact AutomorphicForm.IsWeightedOrbitalIntegralOn.unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq (v.adicCompletion K)
    (AutomorphicForm.localHaar K v) (AutomorphicForm.isHaarMeasure_localHaar K v) γ hγ τ₁ h₁
    AutomorphicForm.LocalWeight.weight continuous_weight hwt f hfm hfb hJ₁ hJ₂

end S_AutomorphicForm_eq_of_isWeightedOrbitalIntegral_of_isWeightedOrbitalIntegral_diagonal_of_measure_preimage_localIntegralSet_eq_one
end P2MW
export P2MW.S_AutomorphicForm_eq_of_isWeightedOrbitalIntegral_of_isWeightedOrbitalIntegral_diagonal_of_measure_preimage_localIntegralSet_eq_one (solution)
