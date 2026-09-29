-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.Leray.supportedIn_relHPresheaf_chow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1d4ef836-ba64-53ec-b7d4-d068fbca62da

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow.AlgebraicGeometry TopologicalSpace Opposite CategoryTheory.Limits"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian IsProper LocallyOfFiniteType.isLocallyNoetherian IsAffineOpen.fromSpec_top IsAffine.of_isIso QuasiCompact IsAffine isPullback_morphismRestrict IsAffineOpen.SpecMap_appLE_fromSpec LocallyOfFiniteType Spec Spec.map Scheme QuasiCompact.compactSpace_of_compactSpace Scheme.isoSpec_Spec_inv IsSeparated isAffineOpen_top IsAffineOpen IsNoetherian Scheme.homOfLE_ι Scheme.ΓSpecIso ProjSpace.stdCoverPullback ChowDatumProj OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.Leray.relHPresheaf Scheme.OrderedAffineCoverOf Scheme.OrderedAffineCoverOf.moduleSections Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "d HSucc SupportedIn obj moduleSections Leray.relHPresheaf"
namespace Leray
p2m_export "AlgebraicGeometry.OModulePresheaf.Leray" "restrictToPreimage relAltH relHPresheaf nonempty_relHPresheaf_obj_equiv_of_isAffineOpen"
p2m_open "AlgebraicGeometry.OModulePresheaf.Leray AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

section Local

variable {R : Type u} [CommRing R]

theorem res_res' {V : Scheme.{u}} {O₁ O₂ O₃ : V.Opens} (h12 : O₁ ≤ O₂) (h23 : O₂ ≤ O₃) (x : Γ(V, O₃)) :
    (V.presheaf.map (homOfLE h12).op).hom ((V.presheaf.map (homOfLE h23).op).hom x)
      = (V.presheaf.map (homOfLE (h12.trans h23)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl

theorem res_refl' {V : Scheme.{u}} {O : V.Opens} (h : O ≤ O) (x : Γ(V, O)) :
    (V.presheaf.map (homOfLE h).op).hom x = x := by
  have : (homOfLE h : O ⟶ O) = 𝟙 O := rfl
  rw [this, op_id, V.presheaf.map_id]; rfl

theorem algebraOfHom_compat {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) (W : V.Opens) :
    ∀ c, letI := Scheme.TwoAffineOpenCover.algebraOfHom π W
      algebraMap R Γ(V, W) c = (V.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
        (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
  fun _ => rfl

theorem specMap_algebraMap_eq_fromSpec_comp {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) = hU.fromSpec ≫ f := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  have halg : CommRingCat.ofHom (algebraMap R Γ(X, U))
      = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U (le_top : U ≤ f ⁻¹ᵁ ⊤) := rfl
  rw [halg, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of R))) hU
      (le_top : U ≤ f ⁻¹ᵁ ⊤)]

theorem isNoeth_of_proper [IsNoetherianRing R] {V : Scheme.{u}}
    (π : V ⟶ Spec (CommRingCat.of R)) [IsProper π] : IsNoetherian V := by
  haveI : LocallyOfFiniteType π := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace π
  exact {}

end Local

section RelHPresheafChow

variable {R : Type u} [CommRing R] {Z : Scheme.{u}}
variable (πZ : Z ⟶ Spec (CommRingCat.of R)) (D : ChowDatumProj πZ)

theorem preimage_isAffineOpen {W : Z.Opens} (hW : IsAffineOpen W)
    (hWU : W ≤ D.U) : IsAffineOpen ((Opens.map D.p.base).obj W) := by
  haveI : IsAffine (W : Scheme.{u}) := hW
  haveI : IsAffine (Limits.pullback D.p W.ι) :=
    IsAffine.of_isIso ((Limits.pullback.congrHom rfl (Z.homOfLE_ι hWU).symm).hom ≫
      (Limits.pullbackLeftPullbackSndIso D.p D.U.ι (Z.homOfLE hWU)).inv ≫
      Limits.pullback.snd _ _)
  exact .of_isIso (isPullback_morphismRestrict D.p W).flip.isoPullback.hom

theorem supportedIn_relHPresheaf_chow' [IsSeparated πZ] (b : ℕ) (hb : 1 ≤ b) :
    (relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).SupportedIn
      ⟨(D.U : Set Z)ᶜ, D.U.isOpen.isClosed_compl⟩ := by
  haveI : IsSeparated (D.p ≫ πZ) := inferInstance
  letI : ∀ O : D.V'.Opens, Module R Γ(D.V', O) := Scheme.OrderedAffineCoverOf.moduleSections (D.p ≫ πZ)
  set K' := ProjSpace.stdCoverPullback D.ιN
  intro W hW

  have hWU : (W : Z.Opens) ≤ D.U := fun x hx =>
    not_not.mp fun hc => (Set.ext_iff.mp hW x).mp ⟨hx, hc⟩

  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, (Nat.sub_add_cancel hb).symm⟩

  have haffpW : IsAffineOpen ((Opens.map D.p.base).obj (W : Z.Opens)) :=
    preimage_isAffineOpen πZ D W.2 hWU

  have hacy := Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen (D.p ≫ πZ)
    (restrictToPreimage D.p πZ K' W.2) haffpW b'

  have hsub : Subsingleton ((restrictToPreimage D.p πZ K' W.2).HSucc (D.p ≫ πZ) b') :=
    Submodule.Quotient.subsingleton_iff.mpr
      (Submodule.eq_top_iff'.mpr fun z => hacy z.2)

  obtain ⟨e⟩ := (nonempty_relHPresheaf_obj_equiv_of_isAffineOpen D.p πZ K' W.2).2 b'
  exact e.toEquiv.subsingleton_congr.mpr hsub

end RelHPresheafChow

end AlgebraicGeometry.OModulePresheaf.Leray

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem solution {R : Type u} [CommRing R]
    {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsSeparated πZ] (D : ChowDatumProj πZ) (b : ℕ) (hb : 1 ≤ b) :
    (OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).SupportedIn
      ⟨(D.U : Set Z)ᶜ, D.U.isOpen.isClosed_compl⟩ :=
  AlgebraicGeometry.OModulePresheaf.Leray.supportedIn_relHPresheaf_chow' πZ D b hb

end

end S_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow (solution)
