-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.isSymmetric_tensor_pullback_negMor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/318db050-b806-5b16-bd08-256709a04086

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_isSymmetric_tensor_pullback_negMor

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Polarisation_isSymmetric_tensor_pullback_negMor.AlgebraicGeometry AlgebraicGeometry.Polarisation P2MW.S_AlgebraicGeometry_Polarisation_isSymmetric_tensor_pullback_negMor.AlgebraicGeometry.Polarisation GoodReductionJacobian NeronModelInfra"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.pullbackTensorObjIso"
namespace Polarisation
p2m_export "AlgebraicGeometry.Polarisation" "idPt negMor LocIsoOnBase IsSymmetric"
namespace SymmetrisationAux
p2m_open "AlgebraicGeometry.Polarisation AlgebraicGeometry"

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem inv_natural (L : RelativeGroupLaw S f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have hmul : L.mul t' (schemeHomOverComp ψ hψ (L.inv t x)) (schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural]

  have h : (schemeHomOverComp ψ hψ (L.inv t x) : SchemeHomOver t' f) *
      (schemeHomOverComp ψ hψ x) = 1 := hmul
  exact eq_inv_of_mul_eq_one_left h

theorem inv_inv (L : RelativeGroupLaw S f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f) : L.inv t (L.inv t x) = x := by
  letI := L.pointGroup t
  exact _root_.inv_inv x

theorem negMor_comp_negMor (L : RelativeGroupLaw S f) : negMor f L ≫ negMor f L = 𝟙 A := by

  set n : SchemeHomOver f f := L.inv f (idPt f) with hn
  have hcoe : negMor f L = n.1 := rfl
  have hcomp : schemeHomOverComp n.1 n.2 (idPt f) = n := by
    apply Subtype.ext
    simp [schemeHomOverComp, idPt]
  have key : schemeHomOverComp n.1 n.2 n = idPt f := by
    conv_lhs => rw [hn]
    rw [inv_natural L f f n.1 n.2 (idPt f), hcomp, hn, inv_inv]
  have := congrArg Subtype.val key
  simpa [schemeHomOverComp, idPt, hcoe] using this

noncomputable def pullbackNegNegIso (L : RelativeGroupLaw S f) (𝓛 : A.Modules) :
    (Scheme.Modules.pullback (negMor f L)).obj ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) ≅ 𝓛 :=
  (Scheme.Modules.pullbackComp (negMor f L) (negMor f L)).app 𝓛 ≪≫
    (Scheme.Modules.pullbackCongr (negMor_comp_negMor L)).app 𝓛 ≪≫
      (Scheme.Modules.pullbackId A).app 𝓛

noncomputable def symmetrisationIso (L : RelativeGroupLaw S f) (𝓛 : A.Modules) :
    (Scheme.Modules.pullback (negMor f L)).obj (𝓛 ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛) ≅
      𝓛 ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛 :=
  Scheme.Modules.pullbackTensorObjIso (negMor f L) 𝓛 ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) ≪≫
    whiskerLeftIso ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) (pullbackNegNegIso L 𝓛) ≪≫
      β_ ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) 𝓛

theorem locIsoOnBase_of_iso {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S)) {M M' : X.Modules}
    (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩

end AlgebraicGeometry.Polarisation.SymmetrisationAux

open AlgebraicGeometry.Polarisation.SymmetrisationAux in
theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) (𝓛 : A.Modules) :
    IsSymmetric f L (𝓛 ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛) :=
  locIsoOnBase_of_iso f (symmetrisationIso L 𝓛)

end S_AlgebraicGeometry_Polarisation_isSymmetric_tensor_pullback_negMor
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_isSymmetric_tensor_pullback_negMor (solution)
