-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBounds
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBounds
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:06:15.631999+00:00
-- url     : https://prove2.me/theorems/9ecccb07-266b-432d-9020-d301940a2655
-- title:
--   Schwartz Bruhat Inner Product Self Nonneg Bounds
-- statement:
--   Definitions and structural lemmas for Schwartz Bruhat Inner Product Self Nonneg Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInnerProductSelfNonnegBounds.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Theorems.Thm_GlobalTheory_SW_HaarLevel_intM_iff
import Theorems.Thm_GlobalTheory_SW_HaarLevel_mem_perSub
import Theorems.Thm_GlobalTheory_SW_HaarLevel_relIndex_perSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.IpPos
open NumberField
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.exists_of_mem_perSub {R : ℕ} {x : Matrix κ ι K}
    (hx : x ∈ _root_.GlobalTheory.SW.perSub K κ ι R) :
    ∃ y : Matrix κ ι K, _root_.GlobalTheory.SW.IntM y ∧ x = (R : K) • y := by
  obtain ⟨y, rfl⟩ := (_root_.GlobalTheory.SW.HaarLevel.mem_perSub R x).mp hx
  exact ⟨_root_.GlobalTheory.SW.HaarLevel.incl K κ ι y,
    (_root_.GlobalTheory.SW.HaarLevel.intM_iff _).mpr ⟨y, rfl⟩,
    (Nat.cast_smul_eq_nsmul K R _).symm⟩
def classes (K κ ι : Type) [Field K] (R : ℕ) : Set (Matrix κ ι K ⧸ perSub K κ ι R) :=
  {q | IntM ((R : K) • q.out)}
open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.classes_finite_card {R : ℕ} (hR : 0 < R) :
    (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).Finite ∧
      (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).ncard ≤
      (R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι))) ^ 2 := by
  set L := _root_.GlobalTheory.SW.perSub K κ ι 1
  set H := (_root_.GlobalTheory.SW.perSub K κ ι (1 * (R * R))).addSubgroupOf L
  have hRK : (R : K) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
  have hidx : H.index = (R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι))) ^ 2 := by
    show (_root_.GlobalTheory.SW.perSub K κ ι (1 * (R * R))).relIndex L = _
    rw [_root_.GlobalTheory.SW.HaarLevel.relIndex_perSub 1 (R * R) one_pos, mul_pow, ← sq]
  let g : L →+ Matrix κ ι K ⧸ _root_.GlobalTheory.SW.perSub K κ ι R :=
    (QuotientAddGroup.mk' _).comp
      ((DistribMulAction.toAddMonoidHom (Matrix κ ι K) ((R : K)⁻¹)).comp L.subtype)
  have hker : H ≤ g.ker := by
    intro z hz
    rw [AddMonoidHom.mem_ker]
    obtain ⟨y, hy, hzy⟩ :=
      _root_.GlobalTheory.SW.IpPos.exists_of_mem_perSub (AddSubgroup.mem_addSubgroupOf.mp hz)
    simp only [g, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
      DistribMulAction.toAddMonoidHom_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, hzy, smul_smul]
    rw [show ((R : K))⁻¹ * ((1 * (R * R) : ℕ) : K) = R by push_cast; field_simp]
    exact AddSubgroup.subset_closure ⟨y, hy, rfl⟩
  let F := QuotientAddGroup.lift H g hker
  have hsub : _root_.GlobalTheory.SW.IpPos.classes K κ ι R ⊆ Set.range F := by
    intro q hq
    have hL : (R : K) • q.out ∈ L :=
      AddSubgroup.subset_closure ⟨_, hq, by rw [Nat.cast_one, one_smul]⟩
    refine ⟨QuotientAddGroup.mk ⟨_, hL⟩, ?_⟩
    simp only [F, QuotientAddGroup.lift_mk, g, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
      DistribMulAction.toAddMonoidHom_apply, QuotientAddGroup.mk'_apply, smul_smul,
      inv_mul_cancel₀ hRK, one_smul]
    exact QuotientAddGroup.out_eq' q
  have hfin : Finite (L ⧸ H) := Nat.finite_of_card_ne_zero (by
    rw [← AddSubgroup.index, hidx]; positivity)
  refine ⟨(Set.finite_range F).subset hsub, ?_⟩
  calc (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).ncard ≤ (Set.range F).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_range F)
    _ = Nat.card (Set.range F) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (L ⧸ H) := Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = _ := hidx
end GlobalTheory.SW.IpPos


