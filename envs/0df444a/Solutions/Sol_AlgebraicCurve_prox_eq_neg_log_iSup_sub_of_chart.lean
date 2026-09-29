-- Prove2me | solution 1 for AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c6e428f1-7fe9-533c-99da-41bb73ddae03

import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart

set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve

namespace SupplyLoc

variable {L : Type*} [Field L]

private lemma le_iSup_fin {ι : Type*} [Finite ι] (f : ι → ℝ) (i : ι) : f i ≤ ⨆ k, f k :=
  le_ciSup (Set.finite_range f).bddAbove i

private theorem iSup_eq_one_of_chart (ν : AbsoluteValue L ℝ) {r : ℕ} (x : Fin r → L) (j : Fin r)
    (hxj : x j = 1) (hx : ∀ i, ν (x i) ≤ 1) : (⨆ i, ν (x i)) = 1 := by
  haveI : Nonempty (Fin r) := ⟨j⟩
  refine le_antisymm (ciSup_le hx) ?_
  have h : ν (x j) ≤ ⨆ i, ν (x i) := le_iSup_fin (fun i => ν (x i)) j
  rwa [hxj, ν.map_one] at h

end SupplyLoc

theorem solution {L : Type*} [Field L]
    (ν : AbsoluteValue L ℝ) (hna : IsNonarchimedean ⇑ν) {r : ℕ}
    (x y : Fin r → L) (j : Fin r) (hxj : x j = 1) (hyj : y j = 1)
    (hx : ∀ i, ν (x i) ≤ 1) (hy : ∀ i, ν (y i) ≤ 1) :
    prox ν x y = -Real.log (⨆ i, ν (x i - y i)) := by
  haveI : Nonempty (Fin r) := ⟨j⟩
  have hX : (⨆ i, ν (x i)) = 1 := SupplyLoc.iSup_eq_one_of_chart ν x j hxj hx
  have hY : (⨆ i, ν (y i)) = 1 := SupplyLoc.iSup_eq_one_of_chart ν y j hyj hy
  have hM : (⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1)) = ⨆ i, ν (x i - y i) := by
    refine le_antisymm (ciSup_le fun p => ?_) (ciSup_le fun i => ?_)
    · have hid : x p.1 * y p.2 - x p.2 * y p.1
          = x p.1 * (y p.2 - x p.2) + x p.2 * (x p.1 - y p.1) := by ring
      rw [hid]
      refine (hna _ _).trans (max_le ?_ ?_)
      · rw [ν.map_mul]
        calc ν (x p.1) * ν (y p.2 - x p.2) ≤ 1 * ν (y p.2 - x p.2) :=
              mul_le_mul_of_nonneg_right (hx p.1) (ν.nonneg _)
          _ = ν (x p.2 - y p.2) := by rw [one_mul, ν.map_sub]
          _ ≤ ⨆ i, ν (x i - y i) := SupplyLoc.le_iSup_fin (fun i => ν (x i - y i)) p.2
      · rw [ν.map_mul]
        calc ν (x p.2) * ν (x p.1 - y p.1) ≤ 1 * ν (x p.1 - y p.1) :=
              mul_le_mul_of_nonneg_right (hx p.2) (ν.nonneg _)
          _ = ν (x p.1 - y p.1) := one_mul _
          _ ≤ ⨆ i, ν (x i - y i) := SupplyLoc.le_iSup_fin (fun i => ν (x i - y i)) p.1
    · have hid : x j * y i - x i * y j = -(x i - y i) := by rw [hxj, hyj]; ring
      calc ν (x i - y i) = ν (x j * y i - x i * y j) := by rw [hid, ν.map_neg]
        _ ≤ ⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1) :=
            SupplyLoc.le_iSup_fin (fun p : Fin r × Fin r => ν (x p.1 * y p.2 - x p.2 * y p.1)) (j, i)
  unfold prox
  rw [hX, hY, hM, Real.log_one]
  ring

end S_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart
end P2MW
export P2MW.S_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart (solution)
