-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaBarEnum
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaBarEnum
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:47:07.244258+00:00
-- url     : https://prove2.me/theorems/bdcc0460-2cb7-4d08-b114-bdeebe7373f2
-- title:
--   Alpha Bar Enum
-- statement:
--   Definitions and structural lemmas for Alpha Bar Enum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/AlphaBarEnum.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaPair
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_act_add_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_act_mul_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_act_nat_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_act_one_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_comp_mulMon
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_one_compMon
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_pow_eq_one_of_kill

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Count
variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]
def killSub (A : PolAV (Sp (FractionRing R))) {O : Type} [Ring O] (ρ : RingAct A.A O) (ga : O) :
    Subgroup (TFK (R := R) F ⟶ A.A) :=
  letI := ρ.hom ga
  MonoidHom.ker (IsMonHom.monoidHom (ρ.act ga) (TFK (R := R) F))
theorem mem_killSub (A : PolAV (Sp (FractionRing R))) {O : Type} [Ring O] (ρ : RingAct A.A O) (ga : O)
    (x : TFK (R := R) F ⟶ A.A) : x ∈ killSub F A ρ ga ↔ x ≫ ρ.act ga = 1 := by
  first
    | exact Iff.rfl
    | exact MonoidHom.mem_ker
    | simp [killSub, MonoidHom.mem_ker]
def torsionEquiv (A : PolAV (Sp (FractionRing R))) {O : Type} [CommRing O] (ρ : RingAct A.A O) (N : ℕ)
    (α β u u' : O) (hab : α * β = (N : O)) (huu : u * α + u' * β = 1) :
    {y : TFK (R := R) F ⟶ A.A // y ^ N = 1} ≃ killSub F A ρ α × killSub F A ρ β where
  toFun y := (⟨y.1 ≫ ρ.act (u' * β), by
      have := ρ.hom u'
      rw [mem_killSub, ← act_mul_apply, show α * (u' * β) = u' * (N : O) by rw [← hab]; ring, act_mul_apply,
        act_nat_apply, y.2, one_compMon]⟩,
    ⟨y.1 ≫ ρ.act (u * α), by
      have := ρ.hom u
      rw [mem_killSub, ← act_mul_apply, show β * (u * α) = u * (N : O) by rw [← hab]; ring, act_mul_apply,
        act_nat_apply, y.2, one_compMon]⟩)
  invFun zw := ⟨zw.1.1 * zw.2.1, by
    have := ρ.hom (N : O)
    rw [← act_nat_apply ρ, comp_mulMon, act_nat_apply, act_nat_apply,
      pow_eq_one_of_kill ρ (show β * α = (N : O) by rw [mul_comm]; exact hab) _ zw.1.2,
      pow_eq_one_of_kill ρ hab _ zw.2.2, _root_.mul_one]⟩
  left_inv y := by
    apply Subtype.ext
    show y.1 ≫ ρ.act (u' * β) * y.1 ≫ ρ.act (u * α) = y.1
    rw [← act_add_apply, add_comm, huu, act_one_apply]
  right_inv zw := by
    obtain ⟨⟨z, hz⟩, ⟨w, hw⟩⟩ := zw
    have hz' : z ≫ ρ.act (u * α) = 1 := by
      have := ρ.hom u
      rw [act_mul_apply, (mem_killSub F A ρ α z).1 hz, one_compMon]
    have hw' : w ≫ ρ.act (u' * β) = 1 := by
      have := ρ.hom u'
      rw [act_mul_apply, (mem_killSub F A ρ β w).1 hw, one_compMon]
    have hz2 : z ≫ ρ.act (u' * β) = z := by
      conv_rhs => rw [← act_one_apply ρ z, ← huu, act_add_apply, hz', _root_.one_mul]
    have hw2 : w ≫ ρ.act (u * α) = w := by
      conv_rhs => rw [← act_one_apply ρ w, ← huu, act_add_apply, hw', _root_.mul_one]
    have := ρ.hom (u' * β)
    have := ρ.hom (u * α)
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show (z * w) ≫ ρ.act (u' * β) = z
      rw [comp_mulMon, hz2, hw', _root_.mul_one]
    · show (z * w) ≫ ρ.act (u * α) = w
      rw [comp_mulMon, hz', hw2, _root_.one_mul]
end Count
end ReciprocityTheory.ChartRestriction.G.H1


