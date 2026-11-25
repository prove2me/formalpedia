-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T14:39:35.298863+00:00
-- url     : https://prove2.me/theorems/4c1f3f34-4c03-4d1c-b450-9bd060df3011
-- title:
--   Dual Map SOf Id To Ring Hom
-- statement:
--   Definitions and structural lemmas for Dual Map SOf Id To Ring Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSOfIdToRingHom.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
section Dual
variable {S : Type} [CommRing S] (s : S)
abbrev dAway : DualNumber S →+* DualNumber (Localization.Away s) := dualMapR (algebraMap S (Localization.Away s))
theorem eq_inl_add_inr {R : Type} [CommRing R] (x : DualNumber R) :
    x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inl x.snd * TrivSqZeroExt.inr 1 := by
  ext <;> simp
theorem dAway_inl (a : S) : dAway s (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (algebraMap S _ a) := by
  ext <;> simp [dAway, dualMapR]
theorem dAway_lift {T : Type} [CommRing T] (gg : DualNumber S →+* T) (hu : IsUnit (gg (TrivSqZeroExt.inl s))) :
    ∃ χ : DualNumber (Localization.Away s) →+* T, χ.comp (dAway s) = gg := by
  let g0 : S →+* T := gg.comp (TrivSqZeroExt.inlHom S S)
  have hu0 : IsUnit (g0 s) := hu
  let φ : Localization.Away s →+* T := IsLocalization.Away.lift s hu0
  have hφ : ∀ a : S, φ (algebraMap S _ a) = gg (TrivSqZeroExt.inl a) := fun a =>
    IsLocalization.lift_eq _ a
  let e := gg (TrivSqZeroExt.inr 1)
  have he : e * e = 0 := by
    simp only [e, ← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]
  refine ⟨{ toFun := fun x => φ x.fst + φ x.snd * e
            map_one' := by simp
            map_mul' := fun x y => by
              simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul,
                MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, map_add, map_mul]
              linear_combination (-(φ x.snd * φ y.snd)) * he
            map_zero' := by simp
            map_add' := fun x y => by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add]; ring }, ?_⟩
  refine RingHom.ext fun x => ?_
  conv_rhs => rw [eq_inl_add_inr x]
  simp only [RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, dAway, dualMapR,
    TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add, map_add, map_mul, hφ]
  simp only [zero_mul, add_zero, e]
end Dual
section Iso
variable {S : Type} [CommRing S] (s : S)
abbrev Ld : Type := Localization.Away (TrivSqZeroExt.inl s : DualNumber S)
theorem isUnit_dAway : IsUnit (dAway s (TrivSqZeroExt.inl s)) := by
  rw [dAway_inl]
  exact (IsLocalization.Away.algebraMap_isUnit s).map (TrivSqZeroExt.inlHom _ _)
def toL : DualNumber (Localization.Away s) →+* Ld s :=
  (dAway_lift s (algebraMap (DualNumber S) (Ld s)) (IsLocalization.Away.algebraMap_isUnit _)).choose
def fromL : Ld s →+* DualNumber (Localization.Away s) :=
  IsLocalization.Away.lift (TrivSqZeroExt.inl s) (isUnit_dAway s)
end Iso
section Glue
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
end Glue
end ReciprocityTheory.ChartRestriction.G.Chart


