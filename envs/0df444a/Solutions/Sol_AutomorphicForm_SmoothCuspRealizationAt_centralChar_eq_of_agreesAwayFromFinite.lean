-- Prove2me | solution 1 for AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b7911f38-7e95-5894-8d39-7be75eadffe5

import Mathlib
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_HeckeCharacter_FiniteOrder
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
import Theorems.Thm_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

namespace CCEE4

open IsDedekindDomain

theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (NumberField.AdelicLevel.diagOne a) = a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![(a : A), 1]).det = a
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem det_heckeGen (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)
      = Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (uniformizerUnit K v)) := by
  show Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 K) K v (uniformizerUnit K v)) = _
  unfold heckeGenAt
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  exact det_diagOne _

theorem isLsXiFunction_of_realization {F : Type} [Field F] [NumberField F] (pins : CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F pins Φ) :
    IsLsXiFunction (𝓞 F) F pins.Z R.centralChar R.toFun := by
  have h := R.smoothCusp.1.1
  unfold IsAutomorphicFnAt at h
  exact ((@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ pins.mS pins.μ pins.Z R.centralChar pins.D R.toFun).mp h).1

theorem centralChar_det_gen (K : Type) [Field K] [NumberField K] (D : Set (AdelicGL2 (𝓞 K) K))
    (Φ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) Φ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ R.exceptionalSet) :
    ((R.centralChar ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = Φ.b v := by
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  have h1 := R.central_eigen v hv g₀

  have hls := isLsXiFunction_of_realization _ _ R
  have h2 := hls.central_transform ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ g₀

  have h3 : ((R.centralChar ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * R.toFun g₀
      = Φ.b v * R.toFun g₀ := by
    rw [← h2]; exact h1
  exact mul_right_cancel₀ hg₀ h3

end CCEE4

theorem solution
    (K : Type) [Field K] [NumberField K] (D : Set (AdelicGL2 (𝓞 K) K))
    (Θ Θ' : HeckeEigensystem K ℂ)
    (hΘ : Θ.AgreesAwayFromFinite Θ')
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral R') :
    R.centralChar = R'.centralChar := by
  classical

  obtain ⟨hic₁, hmod₁, hc₁⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
      K D (fun v => heckeGen (𝓞 K) K v) (adelicBox K) Θ.toRawCentral R
  obtain ⟨hic₂, hmod₂, hc₂⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
      K D (fun v => heckeGen (𝓞 K) K v) (adelicBox K) Θ'.toRawCentral R'
  obtain ⟨S₀, hS₀⟩ := hΘ.toRawCentral
  have key := HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq K
    (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) (R'.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom)
    hic₁ hic₂ (hc₁ hR) (hc₂ hR') _ _ hmod₁ hmod₂ (S₀ ∪ R.exceptionalSet ∪ R'.exceptionalSet) (by
      intro v hv
      simp only [Finset.mem_union, not_or] at hv
      obtain ⟨⟨hv0, hv1⟩, hv2⟩ := hv
      apply Units.ext
      rw [← CCEE4.det_heckeGen]
      simp only [MonoidHom.coe_comp, Function.comp_apply]
      have e1 := CCEE4.centralChar_det_gen K D Θ.toRawCentral R v hv1
      have e2 := CCEE4.centralChar_det_gen K D Θ'.toRawCentral R' v hv2
      have e3 : Θ.toRawCentral.b v = Θ'.toRawCentral.b v := (hS₀ v hv0).2
      convert e1.trans (e3.trans e2.symm) using 2
      rfl
      rfl)

  ext z
  have := congrArg (fun χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ => ((χ (z : (AdeleRing (𝓞 K) K)ˣ) : ℂˣ) : ℂ)) key
  simp at this
  exact this

end S_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite
end P2MW
export P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite (solution)
