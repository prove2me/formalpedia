-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.associator_hom_app_tensorSections_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3e805ef7-784c-537d-aa4d-594ac023fcde

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_associator_hom_app_tensorSections_monoidalV2
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_associator_hom_app_tensorSections_monoidalV2.AlgebraicGeometry"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom Scheme Scheme.Modules.Hom.app Scheme.Modules Scheme.Modules.tensorSections"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Hom Γ Hom.app Modules.Hom Modules.Hom.app Modules Opens PresheafOfModules Modules.sheafify Modules.tensorSections"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom Hom.app sheafify tensorSections sheafify_mu_app_tensorSections_monoidalV2 tensorHom_app_tensorSections_monoidalV2"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace AssocSections

open Opposite TensorProduct

variable {X : Scheme.{u}}

abbrev adj (X : Scheme.{u}) := SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

abbrev ι (X : Scheme.{u}) := SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

abbrev eta (P : X.PresheafOfModules) (U : X.Opens) (x : P.obj (op U)) : Γ((Modules.sheafify X).obj P, U) :=
  ((adj X).unit.app P).app (op U) x

lemma comp_app_apply {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C) (U : X.Opens) (a : Γ(A, U)) :
    (f ≫ g).app U a = g.app U (f.app U a) := rfl

lemma id_app_apply {A : X.Modules} (U : X.Opens) (a : Γ(A, U)) : (𝟙 A : A ⟶ A).app U a = a := rfl

lemma iso_app_injective {A B : X.Modules} (e : A ≅ B) (U : X.Opens) : Function.Injective (e.hom.app U) := by
  intro a b h
  have h2 := congrArg (e.inv.app U) h
  rw [← comp_app_apply, ← comp_app_apply, e.hom_inv_id, id_app_apply, id_app_apply] at h2
  exact h2

lemma whiskerLeft_app_tensorSections {L M M' : X.Modules} (f : M ⟶ M') {U : X.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    (L ◁ f).app U (tensorSections s t) = tensorSections s (f.app U t) := by
  rw [← id_tensorHom, tensorHom_app_tensorSections_monoidalV2]
  rfl

lemma whiskerRight_app_tensorSections {L L' M : X.Modules} (f : L ⟶ L') {U : X.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    (f ▷ M).app U (tensorSections s t) = tensorSections (f.app U s) t := by
  rw [← tensorHom_id, tensorHom_app_tensorSections_monoidalV2]
  rfl

lemma sheafify_map_app_eta {P P' : X.PresheafOfModules} (g : P ⟶ P') (U : X.Opens) (z : P.obj (op U)) :
    ((Modules.sheafify X).map g).app U (eta P U z) = eta P' U (g.app (op U) z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app (op U) z) :)

lemma counit_app_eta (N : X.Modules) (U : X.Opens) (y : Γ(N, U)) :
    Scheme.Modules.Hom.app (M := (Modules.sheafify X).obj ((ι X).obj N)) (N := N)
      ((adj X).counit.app N) U (eta ((ι X).obj N) U y) = y := by
  have h := (adj X).right_triangle_components N
  exact (congr($(h).app (op U) y) :)

theorem associator_sheafify (P Q R : X.PresheafOfModules) (U : X.Opens)
    (x : P.obj (op U)) (y : Q.obj (op U)) (z : R.obj (op U)) :
    (α_ ((Modules.sheafify X).obj P) ((Modules.sheafify X).obj Q) ((Modules.sheafify X).obj R)).hom.app U
        (tensorSections (tensorSections (eta P U x) (eta Q U y)) (eta R U z)) =
      tensorSections (eta P U x) (tensorSections (eta Q U y) (eta R U z)) := by
  let F := Modules.sheafify X
  apply iso_app_injective
    (whiskerLeftIso (F.obj P) (Functor.Monoidal.μIso F Q R) ≪≫ Functor.Monoidal.μIso F P (Q ⊗ R)) U
  have hassoc := Functor.LaxMonoidal.associativity F P Q R
  rw [Iso.trans_hom, whiskerLeftIso_hom, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_hom]
  rw [← comp_app_apply, ← hassoc, comp_app_apply, comp_app_apply, whiskerRight_app_tensorSections,
    sheafify_mu_app_tensorSections_monoidalV2, sheafify_mu_app_tensorSections_monoidalV2,
    sheafify_map_app_eta, comp_app_apply, whiskerLeft_app_tensorSections,
    sheafify_mu_app_tensorSections_monoidalV2, sheafify_mu_app_tensorSections_monoidalV2]
  rfl

theorem associator_hom_app_tensorSections {L M N : X.Modules} {U : X.Opens}
    (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    (α_ L M N).hom.app U (tensorSections (L := L ⊗ M) (M := N) (tensorSections l m) n) =
      tensorSections (L := L) (M := M ⊗ N) l (tensorSections m n) := by
  let εL : (Modules.sheafify X).obj ((ι X).obj L) ⟶ L := (adj X).counit.app L
  let εM : (Modules.sheafify X).obj ((ι X).obj M) ⟶ M := (adj X).counit.app M
  let εN : (Modules.sheafify X).obj ((ι X).obj N) ⟶ N := (adj X).counit.app N
  have hnat := MonoidalCategory.associator_naturality εL εM εN
  have hl : εL.app U (eta ((ι X).obj L) U l) = l := counit_app_eta L U l
  have hm : εM.app U (eta ((ι X).obj M) U m) = m := counit_app_eta M U m
  have hn : εN.app U (eta ((ι X).obj N) U n) = n := counit_app_eta N U n
  have h1 : ((εL ⊗ₘ εM) ⊗ₘ εN).app U
      (tensorSections (tensorSections (eta ((ι X).obj L) U l) (eta ((ι X).obj M) U m)) (eta ((ι X).obj N) U n)) =
      tensorSections (tensorSections l m) n := by
    rw [tensorHom_app_tensorSections_monoidalV2, tensorHom_app_tensorSections_monoidalV2, hl, hm, hn]
  have h2 : (εL ⊗ₘ (εM ⊗ₘ εN)).app U
      (tensorSections (eta ((ι X).obj L) U l) (tensorSections (eta ((ι X).obj M) U m) (eta ((ι X).obj N) U n))) =
      tensorSections l (tensorSections m n) := by
    rw [tensorHom_app_tensorSections_monoidalV2, tensorHom_app_tensorSections_monoidalV2, hl, hm, hn]
  rw [← h1, ← comp_app_apply, hnat, comp_app_apply, associator_sheafify, h2]

end AssocSections

end AlgebraicGeometry.Scheme.Modules

end

open CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_associator_hom_app_tensorSections_monoidalV2.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_associator_hom_app_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {X : Scheme.{u}} {L M N : X.Modules} {U : X.Opens} (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    (α_ L M N).hom.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections (L := L ⊗ M) (M := N)
          (AlgebraicGeometry.Scheme.Modules.tensorSections l m) n) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (L := L) (M := M ⊗ N) l
        (AlgebraicGeometry.Scheme.Modules.tensorSections m n) :=
  AssocSections.associator_hom_app_tensorSections l m n

end S_AlgebraicGeometry_Scheme_Modules_associator_hom_app_tensorSections_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_associator_hom_app_tensorSections_monoidalV2 (solution)
