-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_forall_inf_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/6cbdf8a1-3b16-5894-b4a0-2ec5ed6a1f58

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_forall_inf_eq_bot
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u v

namespace Ws23ClopenGlue

theorem sections_subsingleton_of_isEmpty {Z : Scheme.{u}} (hZ : IsEmpty ↥Z) (P : Z.Modules) (W : Z.Opens)
    (s t : Γ(P, W)) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (C := Ab) ⟨P.presheaf, Scheme.Modules.isSheaf P⟩ (fun i : Empty => i.elim) W
    (fun i => i.elim) (fun x _ => (hZ.false x).elim) s t (fun i => i.elim)

theorem modules_hom_eq_of_isEmpty {Z : Scheme.{u}} (hZ : IsEmpty ↥Z) {P Q : Z.Modules} (a b : P ⟶ Q) : a = b :=
  Scheme.Modules.hom_ext a b fun W => by
    ext s
    exact sections_subsingleton_of_isEmpty hZ Q W _ _

theorem pullbackComp_id_trans_pullbackCongr_app {Z Y : Scheme.{u}} (ι' : Z ⟶ Y) (hf : 𝟙 Z ≫ ι' = ι') (K : Y.Modules) :
    (Scheme.Modules.pullbackComp (𝟙 Z) ι').app K ≪≫ (Scheme.Modules.pullbackCongr hf).app K =
      (Scheme.Modules.pullbackId Z).app ((Scheme.Modules.pullback ι').obj K) := by
  apply Iso.ext
  have U := Scheme.Modules.pseudofunctor_right_unitality ι'
  have U' := congrArg (fun α => NatTrans.app α K) U
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, eqToHom_app] at U'

  erw [Category.comp_id] at U'
  rw [← Iso.app_inv, Iso.inv_comp_eq] at U'

  rw [Iso.trans_hom, Iso.app_hom (Scheme.Modules.pullbackId Z), U']
  congr 1

theorem mapIso_eq_conj_of_eq_id {Z Y : Scheme.{u}} (ι' : Z ⟶ Y) (p : Z ⟶ Z) (hp : p = 𝟙 Z) (hf : p ≫ ι' = ι')
    (M N : Y.Modules)
    (e : (Scheme.Modules.pullback ι').obj M ≅ (Scheme.Modules.pullback ι').obj N) :
    (Scheme.Modules.pullback p).mapIso e =
      ((Scheme.Modules.pullbackComp p ι').app M ≪≫ (Scheme.Modules.pullbackCongr hf).app M) ≪≫ e ≪≫
        ((Scheme.Modules.pullbackComp p ι').app N ≪≫ (Scheme.Modules.pullbackCongr hf).app N).symm := by
  subst hp
  rw [pullbackComp_id_trans_pullbackCongr_app ι' hf M, pullbackComp_id_trans_pullbackCongr_app ι' hf N]
  apply Iso.ext
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  exact (NatIso.naturality_2 (Scheme.Modules.pullbackId Z) e.hom).symm

end Ws23ClopenGlue

open Ws23ClopenGlue

theorem solution
    {X : Scheme.{u}} (M N : X.Modules) {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥)
    (e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ≅ (Scheme.Modules.pullback (U i).ι).obj N) :
    ∃! φ : M ≅ N, ∀ i, (Scheme.Modules.pullback (U i).ι).mapIso φ = e i := by
  classical
  refine Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top M N U hU ?_ e ?_
  · intro i j
    by_cases hij : i = j
    · subst hij
      exact le_iSup_of_le (⟨i, le_inf le_rfl le_rfl⟩ : {k : ι // U k ≤ U i ⊓ U i}) inf_le_left
    · rw [hdisj i j hij]
      exact bot_le
  · intro i j h
    by_cases hij : i = j
    · subst hij
      exact mapIso_eq_conj_of_eq_id (U i).ι (X.homOfLE h) (Scheme.homOfLE_rfl X (U i)) (X.homOfLE_ι h) M N (e i)
    · have hbot : U j = ⊥ := by
        have hij' := hdisj i j hij
        exact le_bot_iff.mp (hij' ▸ (le_inf h le_rfl : U j ≤ U i ⊓ U j))
      have hZ : IsEmpty ↥((U j).toScheme) := ⟨fun x => by
        have hx : (U j).ι.base x ∈ Set.range (U j).ι.base := Set.mem_range_self x
        rw [Scheme.Opens.range_ι] at hx
        have h2 : ((U j : X.Opens) : Set ↥X) = ((⊥ : X.Opens) : Set ↥X) := by rw [hbot]
        rw [h2] at hx
        exact hx⟩
      exact Iso.ext (modules_hom_eq_of_isEmpty hZ _ _)

end S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_forall_inf_eq_bot
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_forall_inf_eq_bot (solution)
