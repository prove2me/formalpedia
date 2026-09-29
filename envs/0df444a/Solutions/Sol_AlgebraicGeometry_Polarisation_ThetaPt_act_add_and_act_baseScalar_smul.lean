-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.ThetaPt.act_add_and_act_baseScalar_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2dd8141b-4b02-574f-b462-36aa5c31c60f

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_act_add_and_act_baseScalar_smul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

namespace K77TH3
namespace ActLinear

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
  {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))

theorem act_add (θ : ThetaPt f L 𝓛 t) (s s' : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    θ.act (s + s') = θ.act s + θ.act s' := by
  show θ.iso.hom.app _ (Scheme.Modules.pullbackLocalSection _ (s + s')) =
    θ.iso.hom.app _ (Scheme.Modules.pullbackLocalSection _ s) + θ.iso.hom.app _ (Scheme.Modules.pullbackLocalSection _ s')
  rw [Scheme.Modules.pullbackLocalSection_add, map_add]

theorem translate_app_baseScalar (x : SchemeHomOver t f) (r : R) :
    (translate f L t x).app ⊤ (baseScalar f t r) = baseScalar f t r := by
  unfold baseScalar
  conv_rhs => rw [← translate_snd f L t x]
  rfl

theorem act_smul (θ : ThetaPt f L 𝓛 t) (r : R) (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    θ.act (baseScalar f t r • s) = baseScalar f t r • θ.act s := by
  have key : θ.act (baseScalar f t r • s) =
      (((translate f L t θ.pt).app ⊤ (baseScalar f t r)) •
        (θ.iso.hom.app ((translate f L t θ.pt) ⁻¹ᵁ ⊤) (Scheme.Modules.pullbackLocalSection _ s)) :
          Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, (translate f L t θ.pt) ⁻¹ᵁ ⊤)) := by
    show θ.iso.hom.app _ (Scheme.Modules.pullbackLocalSection _ (baseScalar f t r • s)) = _
    rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul]
  rw [key, translate_app_baseScalar]
  rfl

end K77TH3.ActLinear

open K77TH3.ActLinear in
theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (θ : ThetaPt f L 𝓛 t) :
    (∀ s s' : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤), θ.act (s + s') = θ.act s + θ.act s') ∧
      ∀ (r : R) (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)),
        θ.act (baseScalar f t r • s) = baseScalar f t r • θ.act s :=
  ⟨act_add f L 𝓛 t θ, act_smul f L 𝓛 t θ⟩

end S_AlgebraicGeometry_Polarisation_ThetaPt_act_add_and_act_baseScalar_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_act_add_and_act_baseScalar_smul (solution)
