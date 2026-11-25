-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_ResCoresPos
-- name    : GroundTheory_TateCohomology_ResCoresPos
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:50:06.281324+00:00
-- url     : https://prove2.me/theorems/574e543f-fa73-5fe4-8e97-3fb551ee1ce3
-- title:
--   Res Cores Pos
-- statement:
--   Definitions and structural lemmas for Res Cores Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresPos.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_barResolution___f_zero_single_ee18ab47ac91
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
universe u
section Incl
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
noncomputable def barInclF (n : ℕ) :
    free k S (Fin n → S) ⟶ res S.subtype (free k G (Fin n → G)) :=
  freeLift k S (res S.subtype (free k G (Fin n → G)))
    (fun v => Finsupp.single (S.subtype ∘ v) (MonoidAlgebra.single (1 : G) (1 : k)))
set_option backward.isDefEq.respectTransparency false in
lemma barInclF_single (n : ℕ) (v : Fin n → S) (s : S) (r : k) :
    (barInclF S n).hom (Finsupp.single v (MonoidAlgebra.single s r)) =
      Finsupp.single (S.subtype ∘ v) (MonoidAlgebra.single (s : G) r) := by
  simp [barInclF]
omit [Group G] in
lemma contractNth_subtype {G : Type u} [Group G] (S : Subgroup G) {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → S) :
    j.contractNth (· * ·) (Subtype.val ∘ x) = S.subtype ∘ j.contractNth (· * ·) x := by
  funext i
  simp only [Fin.contractNth, Function.comp_apply]
  split_ifs <;> simp
set_option backward.isDefEq.respectTransparency false in
lemma barInclF_comm (j : ℕ) :
    barInclF S (j + 1) ≫ (resFunctor S.subtype).map (barComplex.d k G j) =
      barComplex.d k S j ≫ barInclF S j := by
  refine free_ext _ _ _ _ _ fun x => ?_
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [barInclF_single, barComplex.d_single]
  rw [Rep.resMap_hom_apply, OneMemClass.coe_one, barComplex.d_single]
  rw [map_add, map_sum, barInclF_single]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
  rw [barInclF_single, OneMemClass.coe_one]
  exact congrArg (fun v => Finsupp.single v _) (contractNth_subtype S i x)
set_option backward.isDefEq.respectTransparency false in

noncomputable def barIncl :
    (barResolution k S).complex ⟶ (resBarResolution (k := k) S).complex where
  f n := barInclF S n
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    have h := barInclF_comm (k := k) S j
    simp only [resBarResolution, Functor.mapProjectiveResolution,
      Functor.mapHomologicalComplex_obj_d]
    show barInclF S (j + 1) ≫ resMap S.subtype ((barComplex k G).d (j + 1) j) =
      (barComplex k S).d (j + 1) j ≫ barInclF S j
    rw [barComplex.d_def, barComplex.d_def]
    exact h
set_option backward.isDefEq.respectTransparency false in

lemma barIncl_π : barIncl (k := k) S ≫ (resBarResolution (k := k) S).π = (barResolution k S).π := by
  ext : 1
  refine free_ext _ _ _ _ _ fun x => ?_
  simp only [barIncl, resBarResolution, Functor.mapProjectiveResolution, HomologicalComplex.comp_f,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  simp
  erw [barInclF_single]
  erw [barResolution_π_f_zero_single (k := k) (G := G)]
  erw [barResolution_π_f_zero_single (k := k) (G := S)]
noncomputable def barInclHomotopy :
    Homotopy ((barHomotopyEquiv (k := k) S).inv ≫ barIncl S) (𝟙 _) :=
  ProjectiveResolution.liftHomotopy (𝟙 _) _ _
    (by rw [Category.assoc, barIncl_π, barHomotopyEquiv, ProjectiveResolution.homotopyEquiv_inv_π,
      CategoryTheory.Functor.map_id, Category.comp_id])
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp])
end Incl
section Key
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
set_option backward.isDefEq.respectTransparency false in

noncomputable def resHomComplex (A : Rep.{u} k G) :
    (barComplex k G).linearYonedaObj k A ⟶
      (resBarResolution (k := k) S).complex.linearYonedaObj k (res S.subtype A) where
  f n := ModuleCat.ofHom
    { toFun := fun f => (resFunctor S.subtype).map f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm' i j hij := by
    ext f
    simp [resBarResolution, Functor.mapProjectiveResolution]
    rfl
end Key
section Compare
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]
end Compare
end GroundTheory.GroupCoh


