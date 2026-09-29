-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.hasPrincipalRoot_of_isCanonicalPolData_of_locIsoOnBase_tensor_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/47b8aab5-cfe0-525d-bfe6-cc928e352b63

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_hasPrincipalRoot_of_isCanonicalPolData_of_locIsoOnBase_tensor_three

set_option autoImplicit false

open scoped Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme"

namespace RootPow

open AlgebraicGeometry.Scheme.Modules

variable {S : Type} [CommRing S] {X : Scheme.{0}}

theorem locIsoOnBase_of_iso (g : X ⟶ Spec (CommRingCat.of S)) {M M' : X.Modules} (e : M ≅ M') :
    LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

noncomputable def tensorTensorTensorComm (W X' Y Z : X.Modules) : (W ⊗ X') ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X' ⊗ Z) :=
  α_ _ _ _ ≪≫ (Iso.refl W ⊗ᵢ ((α_ _ _ _).symm ≪≫ (β_ X' Y ⊗ᵢ Iso.refl Z) ≪≫ α_ _ _ _)) ≪≫ (α_ _ _ _).symm

noncomputable def tripleIsoTpow (a : X.Modules) : a ⊗ (a ⊗ a) ≅ Scheme.Modules.tpow a 3 :=
  (α_ a a a).symm ≪≫ (((λ_ a).symm ⊗ᵢ Iso.refl a) ⊗ᵢ Iso.refl a)

noncomputable def cubeIso (a b : X.Modules) :
    (a ⊗ b) ⊗ ((a ⊗ b) ⊗ (a ⊗ b)) ≅ Scheme.Modules.tpow a 3 ⊗ Scheme.Modules.tpow b 3 :=
  (Iso.refl _ ⊗ᵢ tensorTensorTensorComm a b a b) ≪≫ tensorTensorTensorComm a b (a ⊗ a) (b ⊗ b) ≪≫
    (tripleIsoTpow a ⊗ᵢ tripleIsoTpow b)

noncomputable def pullbackTriple {Y : Scheme.{0}} (h : Y ⟶ X) (P : X.Modules) :
    (Scheme.Modules.pullback h).obj (P ⊗ P ⊗ P) ≅
      (Scheme.Modules.pullback h).obj P ⊗ ((Scheme.Modules.pullback h).obj P ⊗ (Scheme.Modules.pullback h).obj P) :=
  pullbackTensorObjIso h _ _ ≪≫ (Iso.refl _ ⊗ᵢ pullbackTensorObjIso h _ _)

theorem locIsoOnBase_pullback_tpow_three {S' : Type} [CommRing S'] {A A' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of S)} (f' : A' ⟶ Spec (CommRingCat.of S')) (h : A' ⟶ A)
    (φ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (comm : h ≫ f = f' ≫ φ)
    {pol P : A.Modules} {L₀ N : A'.Modules}
    (hpol : LocIsoOnBase f pol (P ⊗ P ⊗ P))
    (hroot : LocIsoOnBase f' ((Scheme.Modules.pullback h).obj P) (L₀ ⊗ N)) :
    LocIsoOnBase f' ((Scheme.Modules.pullback h).obj pol) (Scheme.Modules.tpow L₀ 3 ⊗ Scheme.Modules.tpow N 3) := by
  have E := LocIsoOnBase.equivalence f'
  have h1 : LocIsoOnBase f' ((Scheme.Modules.pullback h).obj pol) ((Scheme.Modules.pullback h).obj (P ⊗ P ⊗ P)) :=
    LocIsoOnBase.pullback_of_comp_eq f' h φ comm hpol
  have h2 : LocIsoOnBase f' ((Scheme.Modules.pullback h).obj (P ⊗ P ⊗ P))
      ((Scheme.Modules.pullback h).obj P ⊗ ((Scheme.Modules.pullback h).obj P ⊗ (Scheme.Modules.pullback h).obj P)) :=
    locIsoOnBase_of_iso f' (pullbackTriple h P)
  have h3 : LocIsoOnBase f'
      ((Scheme.Modules.pullback h).obj P ⊗ ((Scheme.Modules.pullback h).obj P ⊗ (Scheme.Modules.pullback h).obj P))
      ((L₀ ⊗ N) ⊗ ((L₀ ⊗ N) ⊗ (L₀ ⊗ N))) :=
    hroot.tensor (hroot.tensor hroot)
  have h4 : LocIsoOnBase f' ((L₀ ⊗ N) ⊗ ((L₀ ⊗ N) ⊗ (L₀ ⊗ N))) (Scheme.Modules.tpow L₀ 3 ⊗ Scheme.Modules.tpow N 3) :=
    locIsoOnBase_of_iso f' (cubeIso L₀ N)
  exact E.trans h1 (E.trans h2 (E.trans h3 h4))

theorem isSymmetric_of_locIsoOnBase_tensor_three {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : GoodReductionJacobian.RelativeGroupLaw S f) {pol P : A.Modules}
    (hP : IsSymmetric f L P) (hpol : LocIsoOnBase f pol (P ⊗ P ⊗ P)) : IsSymmetric f L pol := by
  have E := LocIsoOnBase.equivalence f
  have h1 : LocIsoOnBase f ((Scheme.Modules.pullback (negMor f L)).obj pol) ((Scheme.Modules.pullback (negMor f L)).obj (P ⊗ P ⊗ P)) :=
    LocIsoOnBase.pullback_of_comp_eq f (negMor f L) (𝟙 _) (by rw [negMor_over, Category.comp_id]) hpol
  have h2 : LocIsoOnBase f ((Scheme.Modules.pullback (negMor f L)).obj (P ⊗ P ⊗ P))
      ((Scheme.Modules.pullback (negMor f L)).obj P ⊗ ((Scheme.Modules.pullback (negMor f L)).obj P ⊗
        (Scheme.Modules.pullback (negMor f L)).obj P)) :=
    locIsoOnBase_of_iso f (pullbackTriple (negMor f L) P)
  have h3 : LocIsoOnBase f
      ((Scheme.Modules.pullback (negMor f L)).obj P ⊗ ((Scheme.Modules.pullback (negMor f L)).obj P ⊗
        (Scheme.Modules.pullback (negMor f L)).obj P)) (P ⊗ P ⊗ P) :=
    hP.tensor (hP.tensor hP)
  exact E.trans h1 (E.trans h2 (E.trans h3 (E.symm hpol)))

end RootPow

open RootPow in
theorem solution
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {I : Type} (act : I → (u.A ⟶ u.A)) (act_over : ∀ x : I, act x ≫ u.f = u.f) (star : I → I)
    (polE : u.A.Modules) (hE : CerednikDrinfeld.QM.IsCanonicalPolData u.f u.L act act_over star polE)
    (hloc : LocIsoOnBase u.f u.pol (polE ⊗ polE ⊗ polE)) :
    PolarisedAbelianScheme.HasPrincipalRoot u := by
  obtain ⟨_, _, _, ⟨S', instS', instAlg, hff, hroot⟩, _, _⟩ := hE
  refine ⟨S', instS', instAlg, hff, fun L' hL' => ?_⟩
  obtain ⟨𝓛₀, h𝓛₀, hKT, hloc₀⟩ := hroot L' hL'
  exact ⟨𝓛₀, 3, 3, by norm_num, h𝓛₀, hKT,
    RootPow.locIsoOnBase_pullback_tpow_three _ _ _ pullback.condition hloc hloc₀⟩

end S_AlgebraicGeometry_PolarisedAbelianScheme_hasPrincipalRoot_of_isCanonicalPolData_of_locIsoOnBase_tensor_three
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_hasPrincipalRoot_of_isCanonicalPolData_of_locIsoOnBase_tensor_three (solution)
