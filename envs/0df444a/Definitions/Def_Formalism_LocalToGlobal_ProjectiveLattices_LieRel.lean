-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieRel
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_LieRel
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:36:51.620472+00:00
-- url     : https://prove2.me/theorems/1cd8b4ec-0235-4371-881d-96df5e53d1b4
-- title:
--   Lie Rel
-- statement:
--   Definitions and structural lemmas for Lie Rel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieRel.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_list_prod_tan__79ee0da3542e
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_one_left__f4b8b6e904c4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_eq_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_exists_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_exists_w
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_pre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_tmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Formalism.L2.Pj.LieRel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tcoord tmap IsUnivChart tvec_tmap tcoord_spec tvec_inj list_prod_tan' tcoord_scale
  tcoord_tvec isTan_tvec isTan_scale tvec_eig_iff scaleD fB Rel liftT viaT rel_exists_w rel_exists_v rel_eq_iff
  rel_prod rel_pre tan_iff eig_iff one_left' sp JetR)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
section Vside
variable {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := V) (JetR V (Fin n) m) ⟶ G} (hx : IsUnivChart G n xc)
theorem epsOver_hom : (epsOver V V).hom = (sp (R₀ := V) (DualNumber V)).hom := rfl
def eV : epsOver V V ⟶ sp (R₀ := V) (DualNumber V) :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans epsOver_hom.symm)
def cvV (y : sp (R₀ := V) (DualNumber V) ⟶ G) : epsOver V V ⟶ G := eV ≫ y
end Vside
section Kside
variable {K : Type} [Field K] {S : Scheme.{0}} {A : Over S} [GrpObj A] (x : Sp K ⟶ S) {G' : Over (Sp K)} [GrpObj G']
  {F1 : G'.left ⟶ A.left} (h1 : IsGrpPullback G' A x F1) {V : Type} [CommRing V] [Algebra V K] {G : Over (Sp V)}
  [GrpObj G] {F2 : G'.left ⟶ G.left} (h2 : IsGrpPullback G' G (fB V K) F2)
abbrev epsAt : Over S := Over.mk (spMap (algebraMap K (DualNumber K)) ≫ x)
theorem epsMul_alg (s : K) :
    spMap (epsMul s) ≫ spMap (algebraMap K (DualNumber K)) = spMap (algebraMap K (DualNumber K)) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun a => by simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
def iotaX : epsAt x ⟶ Over.mk ((viaT (𝟙 (Sp K)) (sp (R₀ := K) (DualNumber K))).hom ≫ x) :=
  Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ ((sp (R₀ := K) (DualNumber K)).hom ≫ 𝟙 _) ≫ x = spMap (algebraMap K (DualNumber K)) ≫ x
    rw [Category.id_comp, Category.comp_id]; rfl)
def phiX : (viaT (𝟙 (Sp K)) (sp (R₀ := K) (DualNumber K)) ⟶ G') →* (epsAt x ⟶ A) :=
  (preHom (iotaX x)).comp (pushHom h1 _)
def RelA (F1 : G'.left ⟶ A.left) (F2 : G'.left ⟶ G.left) (v : epsAt x ⟶ A)
    (y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G) : Prop :=
  ∃ w : viaT (𝟙 (Sp K)) (sp (R₀ := K) (DualNumber K)) ⟶ G', Rel (F := F2) (𝟙 _) (fB V K) w y ∧ v.left = w.left ≫ F1
def sclA (s : K) : epsAt x ⟶ epsAt x := Over.homMk (spMap (epsMul s)) (by
  show spMap (epsMul s) ≫ spMap (algebraMap K (DualNumber K)) ≫ x = spMap (algebraMap K (DualNumber K)) ≫ x
  rw [← Category.assoc, epsMul_alg])
end Kside
end Formalism.L2.Pj.LieRel


