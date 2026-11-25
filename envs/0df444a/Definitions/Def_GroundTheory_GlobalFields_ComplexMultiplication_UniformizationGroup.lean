-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationGroup
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_UniformizationGroup
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:20:54.316942+00:00
-- url     : https://prove2.me/theorems/715e60f9-7aa9-5351-9f50-331365becdb6
-- title:
--   Uniformization Group
-- statement:
--   Definitions and structural lemmas for Uniformization Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationGroup.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub
import Theorems.Thm_GroundTheory_Global_Elliptic_derivWeierstrassP_add
import Theorems.Thm_GroundTheory_Global_Elliptic_derivWeierstrassP_two_mul
import Theorems.Thm_GroundTheory_Global_Elliptic_equation_weierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_isPeriodic_derivWeierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_isPeriodic_weierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_torusOrder_mk
import Theorems.Thm_GroundTheory_Global_Elliptic_two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCurve_equation_iff
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassP_add
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassP_two_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
open WeierstrassCurve.Affine
variable {L : PeriodPair}
theorem exists_weierstrassP_eq (c : ℂ) : ∃ z, z ∉ L.lattice ∧ ℘[L] z = c := by
  by_contra hcon
  push_neg at hcon
  have h2 := finsum_toNat_torusOrder_weierstrassP_sub (L := L) c
  have h0 : ∀ x : Torus L, (torusOrder L (fun w ↦ ℘[L] w - c) x).toNat = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := Torus.mk_surjective L x
    rw [torusOrder_mk (isEllipticFunction_weierstrassP_sub c)]
    by_cases hz : z ∈ L.lattice
    · have hc : MeromorphicAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicAt
      have e : (fun w ↦ ℘[L] w - c) = ℘[L] + fun _ ↦ -c := by
        funext w
        simp [sub_eq_add_neg]
      have hlt : meromorphicOrderAt ℘[L] z < meromorphicOrderAt (fun _ : ℂ ↦ -c) z := by
        rw [L.order_weierstrassP z hz]
        exact lt_of_lt_of_le (by decide) analyticAt_const.meromorphicOrderAt_nonneg
      rw [e, meromorphicOrderAt_add_eq_left_of_lt hc hlt, L.order_weierstrassP z hz]
      rfl
    · have ha : AnalyticAt ℂ (fun w ↦ ℘[L] w - c) z :=
        (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
      have h0 : analyticOrderAt (fun w ↦ ℘[L] w - c) z = 0 :=
        ha.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 (hcon z hz))
      rw [ha.meromorphicOrderAt_eq, h0]
      rfl
  simp [h0] at h2
variable (L) in

def toPoint (z : ℂ) : (weierstrassCurve L).toAffine.Point :=
  haveI := Classical.propDecidable (z ∈ L.lattice)
  if h : z ∈ L.lattice then 0 else
    .some (℘[L] z) (℘'[L] z / 2) (equation_iff_nonsingular.1 (equation_weierstrassP L h))
lemma toPoint_of_mem {z : ℂ} (h : z ∈ L.lattice) : toPoint L z = 0 := by
  rw [toPoint, dif_pos h]
lemma toPoint_of_notMem {z : ℂ} (h : z ∉ L.lattice) :
    toPoint L z = .some (℘[L] z) (℘'[L] z / 2)
      (equation_iff_nonsingular.1 (equation_weierstrassP L h)) := by
  rw [toPoint, dif_neg h]
lemma point_some_congr {x y x' y' : ℂ} {h : (weierstrassCurve L).toAffine.Nonsingular x y}
    {h' : (weierstrassCurve L).toAffine.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx hy
  rfl
@[simp]
lemma toPoint_zero : toPoint L 0 = 0 := toPoint_of_mem L.lattice.zero_mem
lemma toPoint_add_mem {z l : ℂ} (hl : l ∈ L.lattice) : toPoint L (z + l) = toPoint L z := by
  by_cases hz : z ∈ L.lattice
  · rw [toPoint_of_mem hz, toPoint_of_mem (add_mem hz hl)]
  · have hzl : z + l ∉ L.lattice := fun h ↦ hz (by simpa using sub_mem h hl)
    rw [toPoint_of_notMem hz, toPoint_of_notMem hzl]
    exact point_some_congr (isPeriodic_weierstrassP z l hl)
      (by rw [isPeriodic_derivWeierstrassP z l hl])
lemma toPoint_eq_of_sub_mem {z w : ℂ} (h : z - w ∈ L.lattice) : toPoint L z = toPoint L w := by
  simpa using toPoint_add_mem (z := w) h
theorem toPoint_neg (z : ℂ) : toPoint L (-z) = -toPoint L z := by
  by_cases hz : z ∈ L.lattice
  · rw [toPoint_of_mem hz, toPoint_of_mem (neg_mem hz), neg_zero]
  · have hz' : -z ∉ L.lattice := fun h ↦ hz (by simpa using neg_mem h)
    rw [toPoint_of_notMem hz, toPoint_of_notMem hz', Point.neg_some]
    refine point_some_congr (L.weierstrassP_neg z) ?_
    simp [negY, L.derivWeierstrassP_neg]
    ring
theorem toPoint_eq_zero_iff {z : ℂ} : toPoint L z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun h ↦ ?_, toPoint_of_mem⟩
  by_contra hz
  rw [toPoint_of_notMem hz] at h
  exact Point.some_ne_zero _ h
theorem toPoint_add (z w : ℂ) : toPoint L (z + w) = toPoint L z + toPoint L w := by
  by_cases hz : z ∈ L.lattice
  · rw [toPoint_of_mem hz, zero_add, add_comm, toPoint_add_mem hz]
  by_cases hw : w ∈ L.lattice
  · rw [toPoint_of_mem hw, add_zero, toPoint_add_mem hw]
  by_cases hzw' : z + w ∈ L.lattice
  · have : toPoint L w = toPoint L (-z) := toPoint_eq_of_sub_mem (by rwa [sub_neg_eq_add, add_comm])
    rw [toPoint_of_mem hzw', this, toPoint_neg, add_neg_cancel]
  by_cases hzw : z - w ∈ L.lattice
  ·
    have hwz : toPoint L w = toPoint L z := toPoint_eq_of_sub_mem (by simpa using neg_mem hzw)
    have h2 : toPoint L (z + w) = toPoint L (2 * z) :=
      toPoint_eq_of_sub_mem (by rw [show z + w - 2 * z = -(z - w) by ring]; exact neg_mem hzw)
    have h2z : 2 * z ∉ L.lattice := fun h ↦ hzw' (by
      rw [show z + w = 2 * z - (z - w) by ring]; exact sub_mem h hzw)
    have hd : ℘'[L] z ≠ 0 := fun h ↦ h2z ((two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero hz).2 h)
    have hy : ℘'[L] z / 2 ≠ (weierstrassCurve L).toAffine.negY (℘[L] z) (℘'[L] z / 2) := by
      simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃, zero_mul, sub_zero]
      intro h
      apply hd
      linear_combination h
    rw [h2, hwz, toPoint_of_notMem hz, toPoint_of_notMem h2z, Point.add_self_of_Y_ne hy]
    have hsl : (weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] z) (℘'[L] z / 2) (℘'[L] z / 2) =
        tangentSlope L z / 2 := by
      have hden : ℘'[L] z / 2 - (weierstrassCurve L).toAffine.negY (℘[L] z) (℘'[L] z / 2) =
          ℘'[L] z := by
        simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
        ring
      rw [slope_of_Y_ne rfl hy, hden]
      simp only [tangentSlope, weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₄]
      field_simp
      ring
    have hx : ℘[L] (2 * z) = (weierstrassCurve L).toAffine.addX (℘[L] z) (℘[L] z)
        ((weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] z) (℘'[L] z / 2) (℘'[L] z / 2)) := by
      rw [hsl, weierstrassP_two_mul hz h2z]
      simp only [addX, weierstrassCurve_a₁, weierstrassCurve_a₂]
      ring
    refine point_some_congr hx ?_
    rw [addY, negAddY, ← hx, hsl, derivWeierstrassP_two_mul hz h2z]
    simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
    ring
  ·
    have hne : ℘[L] z ≠ ℘[L] w := fun h ↦
      (sub_mem_or_add_mem_of_weierstrassP_eq hz hw h).elim hzw hzw'
    rw [toPoint_of_notMem hz, toPoint_of_notMem hw, toPoint_of_notMem hzw',
      Point.add_of_X_ne hne]
    have hsl : (weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2) =
        chordSlope L z w / 2 := by
      rw [slope_of_X_ne hne, chordSlope]
      ring
    have hx : ℘[L] (z + w) = (weierstrassCurve L).toAffine.addX (℘[L] z) (℘[L] w)
        ((weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2)) := by
      rw [hsl, weierstrassP_add hz hw hzw hzw']
      simp only [addX, weierstrassCurve_a₁, weierstrassCurve_a₂]
      ring
    refine point_some_congr hx ?_
    rw [addY, negAddY, ← hx, hsl, derivWeierstrassP_add hz hw hzw hzw']
    simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
    ring
theorem toPoint_surjective : Function.Surjective (toPoint L) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, toPoint_zero⟩
  obtain ⟨z, hz, hx⟩ := exists_weierstrassP_eq (L := L) x
  have hE := (weierstrassCurve_equation_iff L x y).1 h.1
  have hP := L.derivWeierstrassP_sq z hz
  rw [hx] at hP
  have hz' : -z ∉ L.lattice := fun h ↦ hz (by simpa using neg_mem h)
  have hy : (y - ℘'[L] z / 2) * (y + ℘'[L] z / 2) = 0 := by linear_combination hE / 4 - hP / 4
  rcases mul_eq_zero.1 hy with h1 | h1
  · refine ⟨z, ?_⟩
    rw [toPoint_of_notMem hz]
    exact point_some_congr hx (by linear_combination -h1)
  · refine ⟨-z, ?_⟩
    rw [toPoint_of_notMem hz']
    exact point_some_congr (by rw [L.weierstrassP_neg, hx])
      (by rw [L.derivWeierstrassP_neg]; linear_combination -h1)
variable (L) in

def toPointHom : ℂ →+ (weierstrassCurve L).toAffine.Point where
  toFun := toPoint L
  map_zero' := toPoint_zero
  map_add' := toPoint_add
variable (L) in

def torusToPoint : Torus L →+ (weierstrassCurve L).toAffine.Point :=
  QuotientAddGroup.lift L.lattice.toAddSubgroup (toPointHom L) fun _ hl ↦ toPoint_of_mem hl
@[simp]
lemma torusToPoint_mk (z : ℂ) : torusToPoint L (Torus.mk L z) = toPoint L z := rfl
lemma torusToPoint_injective : Function.Injective (torusToPoint L) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨z, rfl⟩ := Torus.mk_surjective L x
  rw [torusToPoint_mk, toPoint_eq_zero_iff] at hx
  exact (QuotientAddGroup.eq_zero_iff z).2 hx
lemma torusToPoint_surjective : Function.Surjective (torusToPoint L) := fun P ↦ by
  obtain ⟨z, hz⟩ := toPoint_surjective (L := L) P
  exact ⟨Torus.mk L z, hz⟩
variable (L) in

def torusEquivPoint : Torus L ≃+ (weierstrassCurve L).toAffine.Point :=
  AddEquiv.ofBijective (torusToPoint L) ⟨torusToPoint_injective, torusToPoint_surjective⟩
end Elliptic
end GroundTheory.Global


