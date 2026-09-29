-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/94f3ac1e-3926-5ded-b4bf-ee6f64b0bb22

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_forall_inf_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u v

namespace IsoGlueOI
p2m_open "AlgebraicGeometry.Scheme.Modules"

theorem pullback_faithful_of_iso {V W : Scheme.{u}} (i : V ≅ W) :
    (Scheme.Modules.pullback i.inv).Faithful := by
  have η : Scheme.Modules.pullback i.inv ⋙ Scheme.Modules.pullback i.hom ≅ 𝟭 _ :=
    Scheme.Modules.pullbackComp i.hom i.inv ≪≫ Scheme.Modules.pullbackCongr i.hom_inv_id ≪≫ Scheme.Modules.pullbackId _
  exact Functor.Faithful.of_comp_iso η

noncomputable def cmp {X Y : Scheme.{u}} (b : Y ⟶ X) [IsOpenImmersion b] :
    Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback (Scheme.Hom.isoOpensRange b).inv ≅
      Scheme.Modules.pullback (Scheme.Hom.opensRange b).ι :=
  Scheme.Modules.pullbackComp (Scheme.Hom.isoOpensRange b).inv b ≪≫
    Scheme.Modules.pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp b)

noncomputable def eT {X Y : Scheme.{u}} (b : Y ⟶ X) [IsOpenImmersion b] {P Q : X.Modules}
    (e : (Scheme.Modules.pullback b).obj P ≅ (Scheme.Modules.pullback b).obj Q) :
    (Scheme.Modules.pullback (Scheme.Hom.opensRange b).ι).obj P ≅
      (Scheme.Modules.pullback (Scheme.Hom.opensRange b).ι).obj Q :=
  ((cmp b).app P).symm ≪≫ (Scheme.Modules.pullback (Scheme.Hom.isoOpensRange b).inv).mapIso e ≪≫ (cmp b).app Q

theorem mapIso_eq_eT_iff {X Y : Scheme.{u}} (b : Y ⟶ X) [IsOpenImmersion b] {P Q : X.Modules}
    (e : (Scheme.Modules.pullback b).obj P ≅ (Scheme.Modules.pullback b).obj Q) (φ : P ≅ Q) :
    (Scheme.Modules.pullback (Scheme.Hom.opensRange b).ι).mapIso φ = eT b e ↔
      (Scheme.Modules.pullback b).mapIso φ = e := by
  have nat := (cmp b).hom.naturality φ.hom
  simp only [Functor.comp_map] at nat
  have h1 : (Scheme.Modules.pullback (Scheme.Hom.opensRange b).ι).mapIso φ =
      ((cmp b).app P).symm ≪≫
        (Scheme.Modules.pullback (Scheme.Hom.isoOpensRange b).inv).mapIso ((Scheme.Modules.pullback b).mapIso φ) ≪≫
        (cmp b).app Q := by
    apply Iso.ext
    simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
    erw [nat]
    first
    | rw [Iso.inv_hom_id_app_assoc]
    | (erw [Iso.inv_hom_id_app_assoc])
    | simp
    | (rw [← Category.assoc]; erw [Iso.inv_hom_id_app]; erw [Category.id_comp])
  rw [h1]
  constructor
  · intro h
    have h2 : (Scheme.Modules.pullback (Scheme.Hom.isoOpensRange b).inv).mapIso ((Scheme.Modules.pullback b).mapIso φ) =
        (Scheme.Modules.pullback (Scheme.Hom.isoOpensRange b).inv).mapIso e := by
      have := congrArg (fun ψ => (cmp b).app P ≪≫ ψ ≪≫ ((cmp b).app Q).symm) h
      simpa [eT] using this
    haveI := pullback_faithful_of_iso (Scheme.Hom.isoOpensRange b)
    exact Iso.ext ((Scheme.Modules.pullback (Scheme.Hom.isoOpensRange b).inv).map_injective (congrArg Iso.hom h2))
  · intro h
    rw [eT, h]

end IsoGlueOI

open IsoGlueOI in
theorem solution
    {X : Scheme.{u}} (M N : X.Modules) {ι : Type v} {Y : ι → Scheme.{u}} (b : ∀ j, Y j ⟶ X)
    [∀ j, IsOpenImmersion (b j)]
    (hcov : ⨆ j, Scheme.Hom.opensRange (b j) = ⊤)
    (hdisj : ∀ j l, j ≠ l → Scheme.Hom.opensRange (b j) ⊓ Scheme.Hom.opensRange (b l) = ⊥)
    (e : ∀ j, (Scheme.Modules.pullback (b j)).obj M ≅ (Scheme.Modules.pullback (b j)).obj N) :
    ∃! φ : M ≅ N, ∀ j, (Scheme.Modules.pullback (b j)).mapIso φ = e j := by
  obtain ⟨φ, hφ, huniq⟩ :=
    AlgebraicGeometry.Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_forall_inf_eq_bot M N
      (fun j => Scheme.Hom.opensRange (b j)) hcov hdisj (fun j => eT (b j) (e j))
  exact ⟨φ, fun j => (mapIso_eq_eT_iff (b j) (e j) φ).mp (hφ j),
    fun ψ hψ => huniq ψ fun j => (mapIso_eq_eT_iff (b j) (e j) ψ).mpr (hψ j)⟩

end S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot (solution)
