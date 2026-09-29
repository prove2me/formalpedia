-- Prove2me | solution 1 for AutomorphicForm.mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1c477853-d7bf-5a5c-8bda-cdec02f140d4

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped ENNReal NNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "localIntegralSet isOpen_localIntegralSet localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localHaar_localIntegralSet localCentralizer localCentralizerBorel IsOrbitalIntegral"
p2m_open "AutomorphicForm"

namespace CentValue

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem scalar_mul_comm (c : (v.adicCompletion K)ˣ) (g : GL (Fin 2) (v.adicCompletion K)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (c : v.adicCompletion K) (fun r => Commute.all _ r) _).eq

theorem conj_scalar (c : (v.adicCompletion K)ˣ) (x : GL (Fin 2) (v.adicCompletion K)) :
    x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * x = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  rw [mul_assoc, scalar_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mem_localCentralizer_scalar (c : (v.adicCompletion K)ˣ) (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact scalar_mul_comm K v c g

theorem secondCountableTopology_localGL : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

def centralizerEquiv (c : (v.adicCompletion K)ˣ) :
    localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≃* GL (Fin 2) (v.adicCompletion K) where
  toFun := Subtype.val
  invFun g := ⟨g, mem_localCentralizer_scalar K v c g⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def centralizerHomeo (c : (v.adicCompletion K)ˣ) :
    localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≃ₜ GL (Fin 2) (v.adicCompletion K) where
  toEquiv := (centralizerEquiv K v c).toEquiv
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

end CentValue

end AutomorphicForm

end

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar.AutomorphicForm"

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : ∃ c : (v.adicCompletion K)ˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegral K v γ τ fv I) :
    letI := AutomorphicForm.localCentralizerBorel K v γ
    I * ((τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v}).toReal : ℂ) =
      fv γ := by
  obtain ⟨c, rfl⟩ := hγ

  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := borelSpace_localGLBorel K v
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion K)) := locallyCompactSpace_localGL K v
  haveI : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := CentValue.secondCountableTopology_localGL K v
  haveI : (localHaar K v).IsHaarMeasure := isHaarMeasure_localHaar K v
  letI : MeasurableSpace (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :=
    localCentralizerBorel K v _
  haveI : BorelSpace (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) := ⟨rfl⟩
  haveI := hτ
  obtain ⟨w, ⟨hw0, hwm, hwc, hsec⟩, rfl⟩ := hI

  simp only [CentValue.conj_scalar] at hsec ⊢
  rw [integral_const_mul]
  by_cases hf : fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0
  · rw [hf, zero_mul, zero_mul]

  set e := CentValue.centralizerHomeo K v c with he_def
  have he : (e : localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) → GL (Fin 2) (v.adicCompletion K))
      = Subtype.val := rfl
  have h1 : ∫ t : localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c), w (e t) ∂τ = 1 := by
    simpa only [he, mul_one] using hsec 1 hf
  haveI hτG : Measure.IsHaarMeasure (Measure.map (⇑e) τ) :=
    (CentValue.centralizerEquiv K v c).isHaarMeasure_map τ continuous_subtype_val (continuous_id.subtype_mk _)

  have huniq := Measure.isMulLeftInvariant_eq_smul (Measure.map (⇑e) τ) (localHaar K v)

  have hmass : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ localIntegralSet K v} =
      ((Measure.map (⇑e) τ).haarScalarFactor (localHaar K v) : ℝ≥0∞) := by
    have hK : MeasurableSet (localIntegralSet K v) := (isOpen_localIntegralSet K v).measurableSet
    have h := congrArg (fun m : Measure (GL (Fin 2) (v.adicCompletion K)) => m (localIntegralSet K v)) huniq
    simp only [Measure.smul_apply, localHaar_localIntegralSet, ENNReal.smul_def, smul_eq_mul, mul_one] at h
    rw [Measure.map_apply e.continuous.measurable hK] at h
    exact h

  have hint : ∫ t : localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c), w (e t) ∂τ =
      ((Measure.map (⇑e) τ).haarScalarFactor (localHaar K v) : ℝ) * ∫ x, w x ∂(localHaar K v) := by
    have h := integral_map_equiv (μ := τ) e.toMeasurableEquiv w
    simp only [Homeomorph.toMeasurableEquiv_coe] at h
    rw [← h]
    conv_lhs => rw [huniq]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have key : (∫ x, w x ∂(localHaar K v)) * ((Measure.map (⇑e) τ).haarScalarFactor (localHaar K v) : ℝ) = 1 := by
    rw [mul_comm, ← hint]
    exact h1
  rw [hmass, integral_complex_ofReal, ENNReal.coe_toReal, mul_assoc, ← Complex.ofReal_mul, key, Complex.ofReal_one,
    mul_one]

end S_AutomorphicForm_mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar
end P2MW
export P2MW.S_AutomorphicForm_mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar (solution)
