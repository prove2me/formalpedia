-- Prove2me | solution 1 for AutomorphicForm.eq_inv_mul_of_isWeightedOrbitalIntegralOn_of_isWeightedOrbitalIntegralOn_smul_infiniteAdeleRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/653f551f-b691-5506-8d2d-ccae2ca212f2

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_IsWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_eq_inv_mul_of_isWeightedOrbitalIntegralOn_of_isWeightedOrbitalIntegralOn_smul_infiniteAdeleRing

set_option autoImplicit false

open MeasureTheory NumberField

attribute [local instance] AutomorphicForm.centralizerBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (γ : GL (Fin 2) (InfiniteAdeleRing K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))) [τ.IsHaarMeasure]
    (c : ℝ) (hc : 0 < c)
    (wt : GL (Fin 2) (InfiniteAdeleRing K) → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))),
      ∀ x : GL (Fin 2) (InfiniteAdeleRing K), wt ((t : GL (Fin 2) (InfiniteAdeleRing K)) * x) = wt x)
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hf : AutomorphicForm.IsArchTestFactor K f)
    (J J' : ℂ) (hJ : AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) ν wt γ τ f J)
    (hJ' : AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) ν wt γ (ENNReal.ofReal c • τ) f J') :
    J' = (c : ℂ)⁻¹ * J := by
  classical
  haveI hsc : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := fun v => by
    letI : NontriviallyNormedField v.Completion := M4aHerbrand.ArchSemilocal.nontriviallyNormedCompletion v
    haveI : ProperSpace v.Completion := ProperSpace.of_locallyCompactSpace v.Completion
    infer_instance
  haveI : SecondCountableTopology (InfiniteAdeleRing K) :=
    (inferInstance : SecondCountableTopology (Π v : InfinitePlace K, v.Completion))
  letI iG : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
  haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf _

  obtain ⟨⟨Φ, hΦ, hfΦ⟩, hfc⟩ := hf
  have hcont : Continuous f := by
    have e : f = fun g => Φ (AutomorphicForm.archEntries K g) := funext hfΦ
    rw [e]
    refine hΦ.continuous.comp (continuous_pi fun i => continuous_pi fun j => ?_)
    exact (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.matrix_elem i j)
  have hfm : Measurable f := hcont.measurable
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hcont

  obtain ⟨w, ⟨hw0, hwm, hws, hw1⟩, hJw⟩ := hJ
  have hc0 : (c : ℝ) ≠ 0 := hc.ne'
  have hsec : AutomorphicForm.IsSectionFnOn (InfiniteAdeleRing K) γ (ENNReal.ofReal c • τ) f (fun x => w x / c) := by
    refine ⟨fun x => div_nonneg (hw0 x) hc.le, hwm.div_const c, hws.comp_left (g := fun r : ℝ => r / c) (by simp),
      fun x hx => ?_⟩
    rw [integral_smul_measure, ENNReal.toReal_ofReal hc.le, integral_div, hw1 x hx, smul_eq_mul, mul_one_div_cancel hc0]
  have hJ'' : AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) ν wt γ (ENNReal.ofReal c • τ) f
      ((c : ℂ)⁻¹ * J) := by
    refine ⟨fun x => w x / c, hsec, ?_⟩
    rw [hJw, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (c : ℂ)⁻¹ * (f (x⁻¹ * γ * x) * (wt x : ℂ) * (w x : ℂ)) = f (x⁻¹ * γ * x) * (wt x : ℂ) * ((w x / c : ℝ) : ℂ)
    push_cast
    ring

  have hcτ : (ENNReal.ofReal c • τ).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul _ (by simpa using hc) (by simp)
  exact AutomorphicForm.IsWeightedOrbitalIntegralOn.unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq (InfiniteAdeleRing K) ν hν γ hγ
    (ENNReal.ofReal c • τ) hcτ wt hwtc hwt f hfm ⟨C, hC⟩ hJ' hJ''

end S_AutomorphicForm_eq_inv_mul_of_isWeightedOrbitalIntegralOn_of_isWeightedOrbitalIntegralOn_smul_infiniteAdeleRing
end P2MW
export P2MW.S_AutomorphicForm_eq_inv_mul_of_isWeightedOrbitalIntegralOn_of_isWeightedOrbitalIntegralOn_smul_infiniteAdeleRing (solution)
