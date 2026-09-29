-- Prove2me | solution 1 for AutomorphicForm.coupled_one_diagUnits2_of_normString_eq_toTensorGL_of_measure_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/30d65573-c9e4-5a5a-9702-53b04ed25eb4

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Theorems.Thm_AutomorphicForm_baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_coupled_one_diagUnits2_of_normString_eq_toTensorGL_of_measure_eq_one
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false
open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

namespace CDUAux

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem nonempty_extension : Nonempty (v.Extension (𝓞 L)) := by
  by_contra h
  rw [not_nonempty_iff] at h
  letI := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  have hsum := Ideal.sum_ramification_inertia_extensions (𝓞 K) K L (𝓞 L) v
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  exact (Module.finrank_pos (R := K) (M := L)).ne' hsum.symm

theorem one_tmul_mem_semiLocalIntegers_iff (x : v.adicCompletion K) :
    ((1 : L) ⊗ₜ[K] x) ∈ AutomorphicForm.semiLocalIntegers K L v ↔ x ∈ v.adicCompletionIntegers K := by
  constructor
  · intro hx
    have hcrit := (AutomorphicForm.baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact
      K L v).2.1 ((1 : L) ⊗ₜ[K] x)
    obtain ⟨w⟩ := nonempty_extension K L v
    have hw := (hcrit.mp hx) w
    have happ : HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v ((1 : L) ⊗ₜ[K] x) w =
        algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x := by
      show HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v ((1 : L) ⊗ₜ[K] x) w = _
      rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul]
    rw [happ] at hw
    have hval : Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x) =
        Valued.v x ^ (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal.ramificationIdx' w.1.asIdeal :=
      HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w x
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hw ⊢
    rw [hval] at hw
    exact (pow_le_one_iff (HeightOneSpectrum.ramificationIdx_ne_zero (𝓞 K) (𝓞 L)
      (algebraMap_injective_of_field_isFractionRing (𝓞 K) (𝓞 L) K L) w.1)).mp hw
  · intro hx
    exact ⟨(1 : 𝓞 L) ⊗ₜ ⟨x, hx⟩, by simp [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul]⟩

theorem toTensorGL_mem_semiLocalIntegralSet_iff (s : GL (Fin 2) (v.adicCompletion K)) :
    AutomorphicForm.toTensorGL K L (v.adicCompletion K) s ∈ AutomorphicForm.semiLocalIntegralSet K L v ↔
      s ∈ AutomorphicForm.localIntegralSet K v := by
  have hentry : ∀ (g : GL (Fin 2) (v.adicCompletion K)) (i j : Fin 2),
      ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j =
        (1 : L) ⊗ₜ[K] (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
    intro g i j
    simp [AutomorphicForm.toTensorGL, Algebra.TensorProduct.includeRight_apply]
  rw [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet, AutomorphicForm.mem_localIntegralSet,
    ← map_inv]
  simp only [hentry, one_tmul_mem_semiLocalIntegers_iff]

end CDUAux

open CDUAux in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (α β : (L ⊗[K] v.adicCompletion K)ˣ)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
      AutomorphicForm.semiLocalIntegralSet K L v} = 1) :
    AutomorphicForm.Coupled K L (v.adicCompletion K) σ (diagUnits2 a b) (diagUnits2 α β) 1 τ τ' := by
  classical

  haveI hTR : IsTopologicalRing (L ⊗[K] v.adicCompletion K) := AutomorphicForm.isTopologicalRing_tensor K L _
  haveI hTG : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := AutomorphicForm.isTopologicalGroup_tensorGL K L _
  letI mG : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := AutomorphicForm.glBorelOf _
  haveI bG : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := AutomorphicForm.borelSpace_glBorelOf _
  letI mT : MeasurableSpace (AutomorphicForm.localCentralizer K v (diagUnits2 a b)) :=
    AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)
  haveI bT : BorelSpace (AutomorphicForm.localCentralizer K v (diagUnits2 a b)) := ⟨rfl⟩
  letI mT' : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β)) :=
    AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)
  haveI bT' : BorelSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β)) := ⟨rfl⟩
  haveI hτi : τ.IsHaarMeasure := hτ
  haveI hτ'i : τ'.IsHaarMeasure := hτ'

  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.locallyCompactSpace_localGL K v
  haveI : SecondCountableTopology (AutomorphicForm.localCentralizer K v (diagUnits2 a b)) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hclosed : IsClosed ((AutomorphicForm.localCentralizer K v (diagUnits2 a b) :
      Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) :=
    Set.isClosed_centralizer _
  haveI : LocallyCompactSpace (AutomorphicForm.localCentralizer K v (diagUnits2 a b)) :=
    hclosed.locallyCompactSpace

  have hdisc : Matrix.trace ((diagUnits2 a b : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) _) ^ 2 -
        4 * Matrix.det ((diagUnits2 a b : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) _) =
        ((a : v.adicCompletion K) - (b : v.adicCompletion K)) ^ 2 := by
    rw [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
    ring
  have hγ : AutomorphicForm.IsRegularSemisimple (diagUnits2 a b) := by
    rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero, hdisc]
    exact pow_ne_zero 2 (sub_ne_zero.mpr fun h => hab (Units.ext h))
  have hNC : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ (diagUnits2 a b) (diagUnits2 α β) 1 := by
    unfold AutomorphicForm.IsNormConjugator
    rw [inv_one, one_mul, mul_one, hN]

  obtain ⟨e, he⟩ :=
    AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator
      K L σ hgen (v.adicCompletion K) (diagUnits2 a b) hγ (diagUnits2 α β) 1 hNC
  have he' : ∀ s : AutomorphicForm.localCentralizer K v (diagUnits2 a b),
      ((e s : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β)) :
        GL (Fin 2) (L ⊗[K] v.adicCompletion K)) = AutomorphicForm.toTensorGL K L (v.adicCompletion K) s := by
    intro s; rw [he s, one_mul, inv_one, mul_one]

  set τ'' : Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b)) := Measure.map e.symm τ' with hτ''
  haveI hH : τ''.IsHaarMeasure := e.symm.isHaarMeasure_map τ'

  have huniq := Measure.isMulLeftInvariant_eq_smul τ'' τ

  set S : Set (AutomorphicForm.localCentralizer K v (diagUnits2 a b)) :=
    {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} with hS
  have hSm : MeasurableSet S :=
    ((AutomorphicForm.isOpen_localIntegralSet K v).preimage continuous_subtype_val).measurableSet
  have hecont : Continuous (⇑e : AutomorphicForm.localCentralizer K v (diagUnits2 a b) →
      AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β)) := e.continuous
  have hsymmcont : Continuous (⇑e.symm : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β) →
      AutomorphicForm.localCentralizer K v (diagUnits2 a b)) := e.symm.continuous
  have hpre : (⇑e.symm : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β) →
      AutomorphicForm.localCentralizer K v (diagUnits2 a b)) ⁻¹' S =
      {t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β) |
        ((t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β)) :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} := by
    ext t
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq]
    rw [← toTensorGL_mem_semiLocalIntegralSet_iff K L v, ← he' (e.symm t), ContinuousMulEquiv.apply_symm_apply]
  have hτ''S : τ'' S = 1 := by
    rw [hτ'', Measure.map_apply hsymmcont.measurable hSm, hpre]
    exact hτ'1
  have hc : τ''.haarScalarFactor τ = 1 := by
    have h := congrArg (fun μ : Measure _ => μ S) huniq
    simp only [Measure.smul_apply, hτ''S, hτ1] at h

    have : ((τ''.haarScalarFactor τ : NNReal) : ENNReal) = 1 := by
      simpa [ENNReal.smul_def, smul_eq_mul] using h.symm
    exact_mod_cast this
  have hττ : τ'' = τ := by rw [huniq, hc, one_smul]

  have hg : Measurable (fun s : AutomorphicForm.localCentralizer K v (diagUnits2 a b) =>
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (s : GL (Fin 2) (v.adicCompletion K))) := by
    have hfun : (fun s : AutomorphicForm.localCentralizer K v (diagUnits2 a b) =>
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (s : GL (Fin 2) (v.adicCompletion K))) =
        fun s => ((e s : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β)) :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := funext fun s => (he' s).symm
    rw [hfun]
    exact (continuous_subtype_val.comp hecont).measurable

  unfold AutomorphicForm.Coupled
  show Measure.map _ τ' = Measure.map _ τ
  rw [← hττ, hτ'', Measure.map_map hg hsymmcont.measurable]
  congr 1
  funext t
  simp only [Function.comp_apply, inv_one, one_mul, mul_one]
  rw [← he' (e.symm t), ContinuousMulEquiv.apply_symm_apply]

end S_AutomorphicForm_coupled_one_diagUnits2_of_normString_eq_toTensorGL_of_measure_eq_one
end P2MW
export P2MW.S_AutomorphicForm_coupled_one_diagUnits2_of_normString_eq_toTensorGL_of_measure_eq_one (solution)
