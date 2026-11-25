-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:55.843109+00:00
-- url     : https://prove2.me/theorems/1fa41b27-84ff-448b-9871-a32f8537deb4
-- title:
--   Weierstrass Curve Point Of Lattice Add Of Generic
-- statement:
--   Definitions and structural lemmas for Weierstrass Curve Point Of Lattice Add Of Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassCurvePointOfLatticeAddOfGeneric.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Theorems.Thm_GlobalTheory_countable_add_mem_periodLattice
import Theorems.Thm_GlobalTheory_countable_periodLattice
import Theorems.Thm_GlobalTheory_derivWeierstrassP_eq_zero_iff
import Theorems.Thm_GlobalTheory_exists_weierstrassP_eq_and_derivWeierstrassP_eq
import Theorems.Thm_GlobalTheory_weierstrassP_add_of_ne_of_deriv_ne_zero
import Theorems.Thm_GlobalTheory_weierstrassP_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair WeierstrassCurve
open scoped Topology
noncomputable section
namespace GlobalTheory
variable (L : PeriodPair)
open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
theorem _root_.GlobalTheory.latticeCurve_nonsingular {z : ℂ} (hz : z ∉ L.lattice) :
    (_root_.GlobalTheory.latticeCurve L).toAffine.Nonsingular (℘[L] z) (℘'[L] z / 2) := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, WeierstrassCurve.Affine.equation_iff]
  have h := derivWeierstrassP_sq L z hz
  simp only [_root_.GlobalTheory.latticeCurve]
  linear_combination h / 4
open Classical in

def latticePoint (z : ℂ) : (latticeCurve L).toAffine.Point :=
  if hz : z ∈ L.lattice then 0 else .some _ _ (latticeCurve_nonsingular L hz)
open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
theorem _root_.GlobalTheory.latticePoint_of_mem {z : ℂ} (hz : z ∈ L.lattice) :
    _root_.GlobalTheory.latticePoint L z = 0 := by
  rw [_root_.GlobalTheory.latticePoint, dif_pos hz]
open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
theorem _root_.GlobalTheory.latticePoint_of_notMem {z : ℂ} (hz : z ∉ L.lattice) :
    _root_.GlobalTheory.latticePoint L z =
      .some (℘[L] z) (℘'[L] z / 2) (_root_.GlobalTheory.latticeCurve_nonsingular L hz) := by
  rw [_root_.GlobalTheory.latticePoint, dif_neg hz]
open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
theorem _root_.GlobalTheory.latticePoint_eq_zero_iff {z : ℂ} :
    _root_.GlobalTheory.latticePoint L z = 0 ↔ z ∈ L.lattice := by
  constructor
  · intro h
    by_contra hz
    rw [_root_.GlobalTheory.latticePoint_of_notMem L hz] at h
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ h
  · exact _root_.GlobalTheory.latticePoint_of_mem L
open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
theorem _root_.GlobalTheory.latticePoint_neg (z : ℂ) :
    _root_.GlobalTheory.latticePoint L (-z) = -_root_.GlobalTheory.latticePoint L z := by
  by_cases hz : z ∈ L.lattice
  · rw [_root_.GlobalTheory.latticePoint_of_mem L hz,
      _root_.GlobalTheory.latticePoint_of_mem L (neg_mem hz), neg_zero]
  · have hz' : -z ∉ L.lattice := fun h => hz (by simpa using neg_mem h)
    rw [_root_.GlobalTheory.latticePoint_of_notMem L hz, _root_.GlobalTheory.latticePoint_of_notMem L hz',
      WeierstrassCurve.Affine.Point.neg_some]
    simp [weierstrassP_neg, derivWeierstrassP_neg, WeierstrassCurve.Affine.negY,
      _root_.GlobalTheory.latticeCurve] <;> ring
open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
theorem _root_.GlobalTheory.latticePoint_surjective :
    Function.Surjective (_root_.GlobalTheory.latticePoint L) := by
  intro P
  cases P with
  | zero => exact ⟨0, _root_.GlobalTheory.latticePoint_of_mem L (zero_mem _)⟩
  | some x y h =>
    have he := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at he
    simp only [_root_.GlobalTheory.latticeCurve] at he
    obtain ⟨z, hz, hx, hy⟩ :=
      _root_.GlobalTheory.exists_weierstrassP_eq_and_derivWeierstrassP_eq L (x := x) (y := 2 * y)
        (by linear_combination 4 * he)
    refine ⟨z, ?_⟩
    rw [_root_.GlobalTheory.latticePoint_of_notMem L hz]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx, by rw [hy]; ring⟩
open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
theorem latticePoint_eq_of_sub_mem_lattice {z w : ℂ} (h : z - w ∈ L.lattice) :
    _root_.GlobalTheory.latticePoint L z = _root_.GlobalTheory.latticePoint L w := by
  by_cases hz : z ∈ L.lattice
  · have hw : w ∈ L.lattice := by simpa using sub_mem hz h
    rw [_root_.GlobalTheory.latticePoint_of_mem L hz, _root_.GlobalTheory.latticePoint_of_mem L hw]
  · have hw : w ∉ L.lattice := fun hw => hz (by simpa using add_mem h hw)
    rw [_root_.GlobalTheory.latticePoint_of_notMem L hz, _root_.GlobalTheory.latticePoint_of_notMem L hw]
    have e1 : ℘[L] z = ℘[L] w := by simpa using weierstrassP_add_coe L w ⟨z - w, h⟩
    have e2 : ℘'[L] z = ℘'[L] w := by simpa using derivWeierstrassP_add_coe L w ⟨z - w, h⟩
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨e1, by rw [e2]⟩
open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
theorem weierstrassP_add_and_deriv_add_of_ne {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hne : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w) = ((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)) ^ 2 / 4 - ℘[L] z - ℘[L] w ∧
    ℘'[L] (z + w) = -((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] (z + w) - ℘[L] z) +
      ℘'[L] z) := by
  have hsub : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hne
  have hsub' : ℘[L] w - ℘[L] z ≠ 0 := sub_ne_zero.mpr hne.symm
  by_cases hw' : ℘'[L] w ≠ 0
  · exact _root_.GlobalTheory.weierstrassP_add_of_ne_of_deriv_ne_zero L hz hw hne hw'
  by_cases hz' : ℘'[L] z ≠ 0
  · obtain ⟨h1, h2⟩ := _root_.GlobalTheory.weierstrassP_add_of_ne_of_deriv_ne_zero L hw hz hne.symm hz'
    rw [add_comm w z] at h1 h2
    refine ⟨?_, ?_⟩
    · rw [h1]
      field_simp
      ring
    · rw [h2]
      field_simp
      ring
  push_neg at hw' hz'
  have h2w : w + w ∈ L.lattice := (_root_.GlobalTheory.derivWeierstrassP_eq_zero_iff L hw).mp hw'
  have h2z : z + z ∈ L.lattice := (_root_.GlobalTheory.derivWeierstrassP_eq_zero_iff L hz).mp hz'
  have hzw : z + w ∉ L.lattice := fun h => hne ((_root_.GlobalTheory.weierstrassP_eq_iff L hz hw).mpr (Or.inr h))
  have hd : ℘'[L] (z + w) = 0 := by
    refine (_root_.GlobalTheory.derivWeierstrassP_eq_zero_iff L hzw).mpr ?_
    have e : z + w + (z + w) = (z + z) + (w + w) := by ring
    rw [e]
    exact add_mem h2z h2w
  have hne2 : ℘[L] (z + w) ≠ ℘[L] w := by
    rw [Ne, _root_.GlobalTheory.weierstrassP_eq_iff L hzw hw, not_or]
    constructor
    · simpa using hz
    · intro h
      apply hz
      have e : z = z + w + w - (w + w) := by ring
      rw [e]
      exact sub_mem h h2w
  have ez := derivWeierstrassP_sq L z hz
  have ew := derivWeierstrassP_sq L w hw
  have es := derivWeierstrassP_sq L (z + w) hzw
  rw [hz'] at ez
  rw [hw'] at ew
  rw [hd] at es
  have k1 : 4 * (℘[L] z ^ 2 + ℘[L] z * ℘[L] w + ℘[L] w ^ 2) = L.g₂ := by
    have e : (℘[L] z - ℘[L] w) * (4 * (℘[L] z ^ 2 + ℘[L] z * ℘[L] w + ℘[L] w ^ 2) - L.g₂) = 0 := by
      linear_combination ew - ez
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hsub)
  have k2 : 4 * (℘[L] (z + w) ^ 2 + ℘[L] (z + w) * ℘[L] w + ℘[L] w ^ 2) = L.g₂ := by
    have e : (℘[L] (z + w) - ℘[L] w) *
        (4 * (℘[L] (z + w) ^ 2 + ℘[L] (z + w) * ℘[L] w + ℘[L] w ^ 2) - L.g₂) = 0 := by
      linear_combination ew - es
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hne2))
  have key : ℘[L] (z + w) = -℘[L] z - ℘[L] w := by
    have hza : ℘[L] z - ℘[L] (z + w) ≠ 0 := by
      intro h
      apply hzw
      have h' := (_root_.GlobalTheory.weierstrassP_eq_iff L hz hzw).mp (sub_eq_zero.mp h)
      rcases h' with h' | h'
      · exact (hw (by simpa using neg_mem h')).elim
      · exfalso
        apply hw
        have e2 : w = z + (z + w) - (z + z) := by ring
        rw [e2]
        exact sub_mem h' h2z
    have e : (℘[L] z - ℘[L] (z + w)) * (4 * (℘[L] z + ℘[L] w + ℘[L] (z + w))) = 0 := by
      linear_combination k1 - k2
    have := (mul_eq_zero.mp e).resolve_left hza
    linear_combination this / 4
  refine ⟨?_, ?_⟩
  · rw [hz', hw', key]
    ring
  · rw [hd, hz', hw']
    ring
open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
theorem latticePoint_add_of_not_mem {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (hsub : z - w ∉ L.lattice) (hadd : z + w ∉ L.lattice) :
    _root_.GlobalTheory.latticePoint L (z + w) =
      _root_.GlobalTheory.latticePoint L z + _root_.GlobalTheory.latticePoint L w := by
  classical
  have hne : ℘[L] z ≠ ℘[L] w := fun h => ((_root_.GlobalTheory.weierstrassP_eq_iff L hz hw).mp h).elim hsub hadd
  have hd : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨h1, h2⟩ := weierstrassP_add_and_deriv_add_of_ne L hz hw hne
  rw [_root_.GlobalTheory.latticePoint_of_notMem L hz, _root_.GlobalTheory.latticePoint_of_notMem L hw,
    _root_.GlobalTheory.latticePoint_of_notMem L hadd]
  rw [WeierstrassCurve.Affine.Point.add_some (fun h => hne h.1)]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  rw [WeierstrassCurve.Affine.slope_of_X_ne hne]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, _root_.GlobalTheory.latticeCurve]
  constructor
  · rw [h1]
    field_simp
    ring
  · rw [h2, h1]
    field_simp
    ring
open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in

theorem _root_.GlobalTheory.latticePoint_add (z w : ℂ) :
    _root_.GlobalTheory.latticePoint L (z + w) =
      _root_.GlobalTheory.latticePoint L z + _root_.GlobalTheory.latticePoint L w := by
  by_cases hz : z ∈ L.lattice
  · rw [_root_.GlobalTheory.latticePoint_of_mem L hz, zero_add]
    exact latticePoint_eq_of_sub_mem_lattice L (by simpa using hz)
  by_cases hw : w ∈ L.lattice
  · rw [_root_.GlobalTheory.latticePoint_of_mem L hw, add_zero]
    exact latticePoint_eq_of_sub_mem_lattice L (by simpa using hw)
  by_cases hs : z + w ∈ L.lattice
  · rw [_root_.GlobalTheory.latticePoint_of_mem L hs,
      latticePoint_eq_of_sub_mem_lattice L (z := w) (w := -z)
        (by rw [sub_neg_eq_add, add_comm]; exact hs),
      _root_.GlobalTheory.latticePoint_neg, add_neg_cancel]
  by_cases hd : z - w ∈ L.lattice
  · rw [latticePoint_eq_of_sub_mem_lattice L (z := w) (w := z)
        (by rw [← neg_sub]; exact neg_mem hd),
      latticePoint_eq_of_sub_mem_lattice L (z := z + w) (w := z + z)
        (by rw [show z + w - (z + z) = -(z - w) by ring]; exact neg_mem hd)]
    have hc : ({u : ℂ | u ∈ L.lattice} ∪ {u | u + u ∈ L.lattice} ∪ {u | u + z ∈ L.lattice} ∪
        {u | u + -z ∈ L.lattice}).Countable := by
      refine (((_root_.GlobalTheory.countable_periodLattice L).union ?_).union
        (_root_.GlobalTheory.countable_add_mem_periodLattice L z)).union (_root_.GlobalTheory.countable_add_mem_periodLattice L (-z))
      refine ((_root_.GlobalTheory.countable_periodLattice L).image (fun x => x / 2)).mono ?_
      intro u hu
      exact ⟨u + u, hu, by ring⟩
    obtain ⟨u, hu⟩ : ∃ u, u ∉ ({u : ℂ | u ∈ L.lattice} ∪ {u | u + u ∈ L.lattice} ∪
        {u | u + z ∈ L.lattice} ∪ {u | u + -z ∈ L.lattice}) := by
      by_contra h
      push_neg at h
      exact not_countable_complex (hc.mono fun u _ => h u)
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hu
    obtain ⟨⟨⟨hu1, hu2⟩, hu3⟩, hu4⟩ := hu
    have hzu : z + u ∉ L.lattice := by rw [add_comm]; exact hu3
    have hzmu : z + -u ∉ L.lattice := fun h => hu4 (by
      have := neg_mem h
      rwa [show -(z + -u) = u + -z by ring] at this)
    have hnu : -u ∉ L.lattice := fun h => hu1 (by simpa using neg_mem h)
    have hzz : z + z ∉ L.lattice := fun h => hs (by
      have := sub_mem h hd
      rwa [show z + z - (z - w) = z + w by ring] at this)
    have e : z + z = (z + u) + (z + -u) := by ring
    rw [e, latticePoint_add_of_not_mem L hzu hzmu
        (by rw [show z + u - (z + -u) = u + u by ring]; exact hu2)
        (by rw [← e]; exact hzz),
      latticePoint_add_of_not_mem L hz hu1 (by rw [sub_eq_add_neg]; exact hzmu) hzu,
      latticePoint_add_of_not_mem L hz hnu (by rw [sub_neg_eq_add]; exact hzu) hzmu,
      _root_.GlobalTheory.latticePoint_neg]
    abel
  · exact latticePoint_add_of_not_mem L hz hw hd hs
def latticePointHom : ℂ →+ (latticeCurve L).toAffine.Point :=
  AddMonoidHom.mk' (latticePoint L) (latticePoint_add L)
@[simp] lemma latticePointHom_apply (z : ℂ) : latticePointHom L z = latticePoint L z := rfl
open Filter PeriodPair WeierstrassCurve in
open scoped Topology in
variable (L : PeriodPair) in
theorem _root_.GlobalTheory.ker_latticePointHom :
    (_root_.GlobalTheory.latticePointHom L).ker = L.lattice.toAddSubgroup := by
  ext z
  rw [AddMonoidHom.mem_ker, _root_.GlobalTheory.latticePointHom_apply,
    _root_.GlobalTheory.latticePoint_eq_zero_iff, Submodule.mem_toAddSubgroup]
def latticePointEquiv : (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ (latticeCurve L).toAffine.Point :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_latticePointHom L).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (latticePoint_surjective L))
end GlobalTheory


