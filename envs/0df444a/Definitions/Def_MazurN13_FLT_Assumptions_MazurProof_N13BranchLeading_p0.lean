-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13BranchLeading_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13BranchLeading_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:07:33.382081+00:00
-- url     : https://prove2.me/theorems/cb0b2a9e-6c8c-47dc-acc1-d59dd6f9f380
-- title:
--   FLT.Assumptions.MazurProof.N13BranchLeading source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13BranchLeading

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13BranchLeading
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13BranchNorm_p0

set_option autoImplicit false




/-!
# Leading pole degree across the two infinity branches

For `p(X) + q(X)Y`, cancellation can raise the order at one infinity, but
it cannot raise the order at both.  The minimum of the two branch orders is
the negative of

`max (deg p) (deg q + 3)`.

The proof is valuation-theoretic.  For arbitrary Laurent series `a,b`, the
pair `a+b, a-b` remembers the smaller of the orders of `a,b`, because `2` is
invertible.  This avoids any coefficient enumeration.
-/

open Polynomial
open scoped LaurentSeries

namespace MazurProof.N13BranchLeading

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem min_orderTop_add_sub (a b : LaurentSeries K) :
    min (a + b).orderTop (a - b).orderTop =
      min a.orderTop b.orderTop := by
  apply le_antisymm
  · apply le_min
    · calc
        min (a + b).orderTop (a - b).orderTop ≤
            ((a + b) + (a - b)).orderTop :=
          HahnSeries.min_orderTop_le_orderTop_add
        _ = (2 * a).orderTop := by ring_nf
        _ = a.orderTop := by
          have htwo : (2 : LaurentSeries K) =
              algebraMap K (LaurentSeries K) (2 : K) :=
            (map_ofNat (algebraMap K (LaurentSeries K)) 2).symm
          rw [htwo, HahnSeries.orderTop_mul]
          simp [HahnSeries.algebraMap_apply',
            HahnSeries.orderTop_single (show (2 : K) ≠ 0 by norm_num)]
    · calc
        min (a + b).orderTop (a - b).orderTop ≤
            ((a + b) - (a - b)).orderTop :=
          HahnSeries.min_orderTop_le_orderTop_sub
        _ = (2 * b).orderTop := by ring_nf
        _ = b.orderTop := by
          have htwo : (2 : LaurentSeries K) =
              algebraMap K (LaurentSeries K) (2 : K) :=
            (map_ofNat (algebraMap K (LaurentSeries K)) 2).symm
          rw [htwo, HahnSeries.orderTop_mul]
          simp [HahnSeries.algebraMap_apply',
            HahnSeries.orderTop_single (show (2 : K) ≠ 0 by norm_num)]
  · apply le_min
    · exact HahnSeries.min_orderTop_le_orderTop_add
    · exact HahnSeries.min_orderTop_le_orderTop_sub

theorem min_order_add_sub_of_ne
    (a b : LaurentSeries K)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hplus : a + b ≠ 0) (hminus : a - b ≠ 0) :
    min (a + b).order (a - b).order = min a.order b.order := by
  have htop := min_orderTop_add_sub K a b
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero ha,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hb,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hplus,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hminus] at htop
  exact WithTop.coe_injective (by
    simpa only [WithTop.coe_min] using htop)

def poleDegree (p q : K[X]) : ℕ :=
  by
    classical
    exact max p.natDegree (if q = 0 then 0 else q.natDegree + 3)

private theorem ySeries_ne_zero : N13Infinity.ySeries K ≠ 0 := by
  intro hzero
  have horder := N13Infinity.ySeries_order K
  rw [hzero, HahnSeries.order_zero] at horder
  norm_num at horder

theorem evalPoly_mul_ySeries_order (q : K[X]) (hq : q ≠ 0) :
    (N13BranchNorm.evalPoly K q * N13Infinity.ySeries K).order =
      -((q.natDegree + 3 : ℕ) : ℤ) := by
  rw [HahnSeries.order_mul
    (N13BranchNorm.evalPoly_ne_zero K hq)
    (ySeries_ne_zero K),
    N13BranchNorm.evalPoly_order K q hq,
    N13Infinity.ySeries_order]
  omega

theorem branch_min_order (p q : K[X])
    (hz : N13BranchNorm.linearFunction K p q ≠ 0) :
    min
        (N13Infinity.coordinateToLaurent K
          (N13BranchNorm.linearFunction K p q)).order
        (N13InfinityMinus.coordinateToLaurentMinus K
          (N13BranchNorm.linearFunction K p q)).order =
      -(poleDegree K p q : ℤ) := by
  have hplus :
      N13Infinity.coordinateToLaurent K
          (N13BranchNorm.linearFunction K p q) ≠ 0 := by
    intro hzero
    apply hz
    apply N13Infinity.coordinateToLaurent_injective K
    simpa using hzero
  have hminus :
      N13InfinityMinus.coordinateToLaurentMinus K
          (N13BranchNorm.linearFunction K p q) ≠ 0 := by
    intro hzero
    apply hz
    apply N13InfinityMinus.coordinateToLaurentMinus_injective K
    simpa using hzero
  have hplus' :
      N13BranchNorm.evalPoly K p +
          N13BranchNorm.evalPoly K q * N13Infinity.ySeries K ≠ 0 := by
    simpa only [N13BranchNorm.coordinateToLaurent_linearFunction] using
      hplus
  have hminus' :
      N13BranchNorm.evalPoly K p -
          N13BranchNorm.evalPoly K q * N13Infinity.ySeries K ≠ 0 := by
    simpa only [N13BranchNorm.coordinateToLaurentMinus_linearFunction] using
      hminus
  rw [N13BranchNorm.coordinateToLaurent_linearFunction,
    N13BranchNorm.coordinateToLaurentMinus_linearFunction]
  by_cases hp : p = 0
  · have hq : q ≠ 0 := by
      intro hq
      apply hz
      simp [N13BranchNorm.linearFunction, hp, hq]
    simp only [hp, map_zero, zero_add, zero_sub, HahnSeries.order_neg,
      min_self]
    rw [evalPoly_mul_ySeries_order K q hq]
    simp [poleDegree, hq]
  · by_cases hq : q = 0
    · simp only [hq, map_zero, zero_mul, add_zero, sub_zero, min_self]
      rw [N13BranchNorm.evalPoly_order K p hp]
      simp [poleDegree]
    · have ha := N13BranchNorm.evalPoly_ne_zero K hp
      have hb : N13BranchNorm.evalPoly K q *
          N13Infinity.ySeries K ≠ 0 :=
        mul_ne_zero (N13BranchNorm.evalPoly_ne_zero K hq)
          (ySeries_ne_zero K)
      rw [min_order_add_sub_of_ne K _ _ ha hb hplus' hminus',
        N13BranchNorm.evalPoly_order K p hp,
        evalPoly_mul_ySeries_order K q hq]
      simp only [poleDegree, hq, if_false]
      omega

/-- A regular function with at most a simple pole at each infinity has no
`Y`-part and is at most linear in `X`.  This is the genus-two replacement
for a coefficient search. -/
theorem eq_zero_and_natDegree_le_one_of_branch_orders
    (p q : K[X])
    (hz : N13BranchNorm.linearFunction K p q ≠ 0)
    (hplus : (-1 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K
        (N13BranchNorm.linearFunction K p q)).order)
    (hminus : (-1 : ℤ) ≤
      (N13InfinityMinus.coordinateToLaurentMinus K
        (N13BranchNorm.linearFunction K p q)).order) :
    q = 0 ∧ p.natDegree ≤ 1 := by
  have hmin : (-1 : ℤ) ≤
      min
        (N13Infinity.coordinateToLaurent K
          (N13BranchNorm.linearFunction K p q)).order
        (N13InfinityMinus.coordinateToLaurentMinus K
          (N13BranchNorm.linearFunction K p q)).order :=
    le_min hplus hminus
  rw [branch_min_order K p q hz] at hmin
  have hdegree : poleDegree K p q ≤ 1 := by
    omega
  have hq : q = 0 := by
    by_contra hq
    simp only [poleDegree, hq, if_false] at hdegree
    omega
  refine ⟨hq, ?_⟩
  simpa only [poleDegree, hq, if_pos, Nat.max_zero] using hdegree

end

end MazurProof.N13BranchLeading


