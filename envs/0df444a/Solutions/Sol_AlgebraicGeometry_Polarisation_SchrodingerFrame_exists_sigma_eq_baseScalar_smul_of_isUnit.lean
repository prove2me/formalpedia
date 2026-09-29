-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.SchrodingerFrame.exists_sigma_eq_baseScalar_smul_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/e5a6dd97-f9bd-5db1-ba00-aa4f2e63d6f1

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_SchrodingerFrame_exists_sigma_eq_baseScalar_smul_of_isUnit

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

universe u

namespace RescaleSol

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
  {𝓛 : A.Modules} {R : Type u} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}

theorem translate_app_baseScalar (x : SchemeHomOver t f) (r : R) :
    (Polarisation.translate f L t x).app ⊤ (Polarisation.baseScalar f t r) = Polarisation.baseScalar f t r := by
  unfold Polarisation.baseScalar
  show ((pullback.snd f t).appTop ≫ (Polarisation.translate f L t x).appTop).hom _ = _
  rw [← Scheme.Hom.comp_appTop, Polarisation.translate_snd]

theorem act_baseScalar_smul (θ : Polarisation.ThetaPt f L 𝓛 t) (r : R)
    (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    θ.act (Polarisation.baseScalar f t r • s) = Polarisation.baseScalar f t r • θ.act s := by
  unfold Polarisation.ThetaPt.act
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul, translate_app_baseScalar]
  rfl

theorem baseScalar_mul (r r' : R) :
    Polarisation.baseScalar f t (r * r') = Polarisation.baseScalar f t r * Polarisation.baseScalar f t r' := by
  unfold Polarisation.baseScalar
  rw [map_mul, map_mul]

end RescaleSol

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {𝓛 : A.Modules} {R : Type u} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}
    {g : ℕ} {δ : Fin g → ℕ} [hδ : ∀ i, NeZero (δ i)]
    (F : Polarisation.SchrodingerFrame f L 𝓛 t δ) (c : R) (hc : IsUnit c) :
    ∃ F' : Polarisation.SchrodingerFrame f L 𝓛 t δ,
      (∀ h, F'.σ h = Polarisation.baseScalar f t c • F.σ h) ∧ F'.lift = F.lift ∧ F'.dualLift = F.dualLift := by
  classical
  obtain ⟨cinv, hcinv⟩ : ∃ cinv : R, c * cinv = 1 := hc.exists_right_inv
  let u : Γ(pullback f t, ⊤) := Polarisation.baseScalar f t c
  refine ⟨{ σ := fun h => u • F.σ h
            basis := ?basis
            lift := F.lift
            dualLift := F.dualLift
            lift_act := ?la
            dualLift_act := ?da }, fun h => rfl, rfl, rfl⟩
  case la =>
    intro h h'
    show (F.lift h).act (Polarisation.baseScalar f t c • F.σ h') = Polarisation.baseScalar f t c • F.σ (h + h')
    rw [RescaleSol.act_baseScalar_smul, F.lift_act]
  case da =>
    intro χ h
    show (F.dualLift χ).act (Polarisation.baseScalar f t c • F.σ h) =
      Polarisation.baseScalar f t (χ h) • (Polarisation.baseScalar f t c • F.σ h)
    rw [RescaleSol.act_baseScalar_smul, F.dualLift_act, smul_smul, smul_smul, mul_comm]
  case basis =>

    have hmul : Function.Bijective fun d : ((i : Fin g) → ZMod (δ i)) → R => fun h => d h * c := by
      refine Function.bijective_iff_has_inverse.mpr ⟨fun d h => d h * cinv, fun d => ?_, fun d => ?_⟩
      · funext h; show d h * c * cinv = d h; rw [mul_assoc, hcinv, mul_one]
      · funext h; show d h * cinv * c = d h; rw [mul_assoc, mul_comm cinv, hcinv, mul_one]
    have key : (fun d : ((i : Fin g) → ZMod (δ i)) → R => ∑ h, Polarisation.baseScalar f t (d h) • (u • F.σ h)) =
        (fun d : ((i : Fin g) → ZMod (δ i)) → R => ∑ h, Polarisation.baseScalar f t (d h) • F.σ h) ∘
          (fun d => fun h => d h * c) := by
      funext d
      show ∑ h, Polarisation.baseScalar f t (d h) • (Polarisation.baseScalar f t c • F.σ h) =
        ∑ h, Polarisation.baseScalar f t (d h * c) • F.σ h
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [smul_smul, RescaleSol.baseScalar_mul]
    rw [key]
    exact F.basis.comp hmul

end S_AlgebraicGeometry_Polarisation_SchrodingerFrame_exists_sigma_eq_baseScalar_smul_of_isUnit
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_SchrodingerFrame_exists_sigma_eq_baseScalar_smul_of_isUnit (solution)
