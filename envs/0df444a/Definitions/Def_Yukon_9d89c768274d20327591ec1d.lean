-- Prove2me | Definitions.Def_Yukon_9d89c768274d20327591ec1d
-- name    : Yukon_9d89c768274d20327591ec1d
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T09:51:09.911607+00:00
-- url     : https://prove2.me/theorems/e6868a1e-c0de-4c06-8984-1976c98963b7
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.PureFlagSliceBudget6807.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.PureFlagSliceBudget6807.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/PureFlagSliceBudget6807.lean
--
--   yukon-proof-operation:foundation-direct-1c9b91ec7a5d1c7b1c7d7d6368397bfba33bd8bc2787f965c947d92fb6b43439
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiM2ZlODE2Y2RhYWFhZTA4YmVlY2JhNzc4YTQxMTJiMjY1NjliOGVlY2FjYTYxMDJlOWNiMGFjMzViNDA2ZjFhMSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTFjOWI5MWVjN2E1ZDFjN2IxYzdkN2Q2MzY4Mzk3YmZiYTMzYmQ4YmMyNzg3Zjk2NWM5NDdkOTJmYjZiNDM0MzkiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl85ZDg5Yzc2ODI3NGQyMDMyNzU5MWVjMWQiLCJ2IjoyfQ]

import Definitions.Def_Yukon_0bbabd56aca9bc076824eff5

/-
UNCOMPILED. Pure-flag budgets for slice components, using the actual pinned
AdaptiveUnitProjectionFamily. No surface moving class is introduced.
-/













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.PureFlagSliceBudget6807
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN026 RCN046 RCN084 RCN095 RCN114
open RCN204 RCN234 RCN237 RCN264 RCN340 RCN341
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {E : Type} [Field E] [IsAlgClosed E]
  {G T H : MvPolynomial (Fin 3) E} {p q : FlagDegree}
  {base : ∀ C : RegularComponent E G T H, SeparableLiteralCoordinate C.1}

/-- These are the SAME three integer costs as the old prime budget. -/
theorem sum_flagPole_le (U : AdaptiveUnitPoleBudget base p q)
    (C : RegularComponent E G T H) (r : FlagDegree)
    (W : Finset (Place E (CoordinateField E C.1))) :
    (∑ v ∈ W, flagPole v.val (coordinate E C.1) r) ≤
      (U.toPrimeFlagBudgetFamily.weightedCost r C : ℤ) := by
  have hz := U.zPole C W
  have hy := U.yzPole C W
  have ha := U.allPole C W
  simp only [exponentSetPoleWeight_unitZ] at hz
  simp only [exponentSetPoleWeight_unitYZ] at hy
  simp only [exponentSetPoleWeight_unitAll] at ha
  have h := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg r.zOnly))
    (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg r.yz)))
    (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg r.all))
  simpa only [flagPole, Finset.sum_add_distrib, ← Finset.mul_sum,
    PrimeFlagBudgetFamily.weightedCost,
    AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily, Nat.cast_add, Nat.cast_mul] using h

theorem weightedCost_add_smul (U : AdaptiveUnitPoleBudget base p q)
    (C : RegularComponent E G T H) (d w : ℕ) (J V : FlagDegree) :
    U.toPrimeFlagBudgetFamily.weightedCost (d • J + w • V) C =
      d * U.toPrimeFlagBudgetFamily.weightedCost J C +
        w * U.toPrimeFlagBudgetFamily.weightedCost V C := by
  simp only [PrimeFlagBudgetFamily.weightedCost]
  change (d*J.zOnly+w*V.zOnly)*U.zCost C +
      (d*J.yz+w*V.yz)*U.yzCost C + (d*J.all+w*V.all)*U.allCost C = _
  dsimp only [AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily]
  ring

/-- Sum over actual active geometric factors using cumulative flag budgets.
It does not assume the three difference coordinates are separately additive. -/
theorem all_active_slice_costs_le (F N R : MvPolynomial (Fin 3) E)
    (hF : F ≠ 0) (p q r : FlagDegree) (hFp : PolynomialInFlag p F)
    (base : ∀ g : ↥(activeFactors F N), ∀ C : RegularComponent E g.1 N R,
      SeparableLiteralCoordinate C.1)
    (U : ∀ g : ↥(activeFactors F N), AdaptiveUnitPoleBudget (base g) (exactFlag g.1) q) :
    (∑ g : ↥(activeFactors F N), ∑ C : RegularComponent E g.1 N R,
      (U g).toPrimeFlagBudgetFamily.weightedCost r C) ≤ flagMixed p q r := by
  exact (Finset.sum_le_sum (fun g _ =>
    (U g).toPrimeFlagBudgetFamily.sum_weightedCost_le r)).trans
      (activeFactors_mixed_sum_le F N hF p q r hFp)

end
end ProximityPrize.SubmissionLower.PureFlagSliceBudget6807


