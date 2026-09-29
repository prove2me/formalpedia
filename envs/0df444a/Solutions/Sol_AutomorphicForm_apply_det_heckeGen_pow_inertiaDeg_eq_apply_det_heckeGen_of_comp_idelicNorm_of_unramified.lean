-- Prove2me | solution 1 for AutomorphicForm.apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a39b2fbf-0d4e-5eaa-bed4-65fd3e22fb37

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.AdelicLevel

namespace CharCompat

theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![(a : A), 1]) = (a : A)
  rw [Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

theorem det_heckeGen (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v) = AutomorphicForm.uniformizerIdele F v := by
  unfold heckeGen heckeGenAt AutomorphicForm.uniformizerIdele
  exact det_diagOne _

def lift {G : Type*} [Group G] (χ : (⊤ : Subgroup G) →* ℂˣ) : G →* ℂˣ :=
  χ.comp (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.toMonoidHom

theorem lift_apply {G : Type*} [Group G] (χ : (⊤ : Subgroup G) →* ℂˣ) (g : G) :
    lift χ g = χ ⟨g, Subgroup.mem_top g⟩ := rfl

end CharCompat

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξKN : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξK ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
        ξL ⟨z, Subgroup.mem_top z⟩)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hvw : HeightOneSpectrum.under (𝓞 K) w = v)
    (hur : ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξK ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1) :
    ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
        v.asIdeal.inertiaDeg' w.asIdeal =
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
  subst hvw
  rw [CharCompat.det_heckeGen K, CharCompat.det_heckeGen L]
  obtain ⟨t, ht1, hN⟩ :=
    M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit K L w
  have h1 : ξL ⟨AutomorphicForm.uniformizerIdele L w, Subgroup.mem_top _⟩ =
      CharCompat.lift ξK ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
        (AutomorphicForm.uniformizerIdele L w)) := by
    rw [CharCompat.lift_apply]; exact (hξKN _).symm
  have h2 : CharCompat.lift ξK ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
        (AutomorphicForm.uniformizerIdele L w)) =
      CharCompat.lift ξK (AutomorphicForm.uniformizerIdele K (HeightOneSpectrum.under (𝓞 K) w)) ^
        (HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal := by
    rw [hN, map_mul, map_pow, CharCompat.lift_apply ξK (Units.map _ _), hur t ht1, mul_one]
  rw [h1, h2, ← CharCompat.lift_apply ξK, Units.val_pow_eq_pow_val]

end S_AutomorphicForm_apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified
end P2MW
export P2MW.S_AutomorphicForm_apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified (solution)
