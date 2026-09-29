-- Prove2me | solution 1 for AlgebraicCurve.prox_eq_zero_of_far_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5ca5ec0b-5d26-56ed-a461-fea119403abe

import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_prox_eq_zero_of_far_of_chart

set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve

namespace SupplyLoc

variable {L : Type*} [Field L]

private lemma le_iSup_fin {ι : Type*} [Finite ι] (f : ι → ℝ) (i : ι) : f i ≤ ⨆ k, f k :=
  le_ciSup (Set.finite_range f).bddAbove i

private lemma add_eq_of_lt (ν : AbsoluteValue L ℝ) (hna : IsNonarchimedean ⇑ν) {z w : L}
    (h : ν z < ν w) : ν (z + w) = ν w := by
  refine le_antisymm ((hna z w).trans (max_le h.le le_rfl)) ?_
  have key := hna (z + w) (-z)
  rw [show z + w + -z = w from by ring, ν.map_neg] at key
  rcases max_cases (ν (z + w)) (ν z) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he] at key; exact key
  · rw [he] at key; exact absurd (lt_of_le_of_lt key h) (lt_irrefl _)

private lemma sub_le_max (ν : AbsoluteValue L ℝ) (hna : IsNonarchimedean ⇑ν) (a b : L) :
    ν (a - b) ≤ max (ν a) (ν b) := by
  have h := hna a (-b)
  rwa [← sub_eq_add_neg, ν.map_neg] at h

private theorem iSup_eq_one_of_chart (ν : AbsoluteValue L ℝ) {r : ℕ} (x : Fin r → L) (j : Fin r)
    (hxj : x j = 1) (hx : ∀ i, ν (x i) ≤ 1) : (⨆ i, ν (x i)) = 1 := by
  haveI : Nonempty (Fin r) := ⟨j⟩
  refine le_antisymm (ciSup_le hx) ?_
  have h : ν (x j) ≤ ⨆ i, ν (x i) := le_iSup_fin (fun i => ν (x i)) j
  rwa [hxj, ν.map_one] at h

end SupplyLoc

theorem solution {L : Type*} [Field L]
    (ν : AbsoluteValue L ℝ) (hna : IsNonarchimedean ⇑ν) {r : ℕ}
    (x y : Fin r → L) (j b : Fin r) (hxj : x j = 1) (hyb : y b = 1)
    (hx : ∀ i, ν (x i) ≤ 1) (hyj : ν (y j) < 1) :
    prox ν x y = 0 := by
  haveI : Nonempty (Fin r) := ⟨j⟩
  have hX : (⨆ i, ν (x i)) = 1 := SupplyLoc.iSup_eq_one_of_chart ν x j hxj hx
  have hjb : ν (x j * y b - x b * y j) = 1 := by
    have hid : x j * y b - x b * y j = -(x b * y j) + 1 := by rw [hxj, hyb]; ring
    have hlt : ν (-(x b * y j)) < ν (1 : L) := by
      rw [ν.map_neg, ν.map_mul, ν.map_one]
      calc ν (x b) * ν (y j) ≤ 1 * ν (y j) := mul_le_mul_of_nonneg_right (hx b) (ν.nonneg _)
        _ = ν (y j) := one_mul _
        _ < 1 := hyj
    rw [hid, SupplyLoc.add_eq_of_lt ν hna hlt, ν.map_one]
  have hM : (⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1)) = ⨆ i, ν (y i) := by
    refine le_antisymm (ciSup_le fun p => ?_) (ciSup_le fun i => ?_)
    · refine (SupplyLoc.sub_le_max ν hna _ _).trans (max_le ?_ ?_)
      · rw [ν.map_mul]
        calc ν (x p.1) * ν (y p.2) ≤ 1 * ν (y p.2) := mul_le_mul_of_nonneg_right (hx p.1) (ν.nonneg _)
          _ = ν (y p.2) := one_mul _
          _ ≤ ⨆ i, ν (y i) := SupplyLoc.le_iSup_fin (fun i => ν (y i)) p.2
      · rw [ν.map_mul]
        calc ν (x p.2) * ν (y p.1) ≤ 1 * ν (y p.1) := mul_le_mul_of_nonneg_right (hx p.2) (ν.nonneg _)
          _ = ν (y p.1) := one_mul _
          _ ≤ ⨆ i, ν (y i) := SupplyLoc.le_iSup_fin (fun i => ν (y i)) p.1
    · by_cases hcmp : ν (x i * y j) < ν (y i)
      · have hid : x j * y i - x i * y j = -(x i * y j) + y i := by rw [hxj]; ring
        have hlt : ν (-(x i * y j)) < ν (y i) := by rwa [ν.map_neg]
        have hcarry : ν (x j * y i - x i * y j) = ν (y i) := by
          rw [hid, SupplyLoc.add_eq_of_lt ν hna hlt]
        calc ν (y i) = ν (x j * y i - x i * y j) := hcarry.symm
          _ ≤ ⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1) :=
              SupplyLoc.le_iSup_fin (fun p : Fin r × Fin r => ν (x p.1 * y p.2 - x p.2 * y p.1)) (j, i)
      · have h1 : ν (y i) ≤ 1 := by
          refine (not_lt.mp hcmp).trans ?_
          rw [ν.map_mul]
          calc ν (x i) * ν (y j) ≤ 1 * ν (y j) := mul_le_mul_of_nonneg_right (hx i) (ν.nonneg _)
            _ = ν (y j) := one_mul _
            _ ≤ 1 := hyj.le
        calc ν (y i) ≤ 1 := h1
          _ = ν (x j * y b - x b * y j) := hjb.symm
          _ ≤ ⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1) :=
              SupplyLoc.le_iSup_fin (fun p : Fin r × Fin r => ν (x p.1 * y p.2 - x p.2 * y p.1)) (j, b)
  unfold prox
  rw [hX, hM, Real.log_one]
  ring

end S_AlgebraicCurve_prox_eq_zero_of_far_of_chart
end P2MW
export P2MW.S_AlgebraicCurve_prox_eq_zero_of_far_of_chart (solution)
