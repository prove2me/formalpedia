-- Prove2me | Definitions.Def_Yukon_2f19922183745f76d5bea98a
-- name    : Yukon_2f19922183745f76d5bea98a
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T11:20:43.439847+00:00
-- url     : https://prove2.me/theorems/691bf4ed-671e-4174-ab73-31cf2363a431
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.SmallSliceBudgets6807.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.SmallSliceBudgets6807.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/SmallSliceBudgets6807.lean
--
--   yukon-proof-operation:foundation-direct-257aa6000cc957d48fb3a45e55b7f0803cd15d422be0395f3e43ab643b3d44a5
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMDY1OGUxNDVjMmQ4YmM2MDIyZjNjNWVjMTc2YzZlNjcyYTA0YzRiMTcyNzFjN2IyMjhiMjQ3ZjFlYzRiMmNjZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTI1N2FhNjAwMGNjOTU3ZDQ4ZmIzYTQ1ZTU1YjdmMDgwM2NkMTVkNDIyYmUwMzk1ZjNlNDNhYjY0M2IzZDQ0YTUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8yZjE5OTIyMTgzNzQ1Zjc2ZDViZWE5OGEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_a957bc9c4724c6765d4efdf5

/-
UNCOMPILED research overlay. Construct the actual slice budgets from the frozen
small-projection theorem. No first-cut or joint-cost inequality is an input.
-/













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.SmallSliceBudgets6807
open scoped Classical BigOperators
open RCN095 RCN237 RCN264 RCN340 RCN341 RCN084 RCN039 RCN046
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
variable {E : Type} [Field E] [IsAlgClosed E]
local notation "Poly" => MvPolynomial (Fin 3) E

/-- Unlike a presumed first-cut bound, this structure records the original
three coordinate pole budgets on all actual active slice factors. -/
structure SliceBudgets (F N R : Poly) (q : FlagDegree) where
  base : ∀ g : ↥(activeFactors F N), ∀ C : RegularComponent E g.1 N R,
    SeparableLiteralCoordinate C.1
  unit : ∀ g : ↥(activeFactors F N),
    AdaptiveUnitPoleBudget (base g) (exactFlag g.1) q

/-- The old generic low-degree gates construct every required pure budget. -/
theorem exists_sliceBudgets (F N R : Poly) (p q : FlagDegree)
    (hF : F ≠ 0) (hFp : PolynomialInFlag p F) (hNq : PolynomialInFlag q N)
    (c : ℕ) [CharP E c] (hdeg : p.zOnly+p.yz+p.all < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c) :
    Nonempty (SliceBudgets F N R q) := by
  classical
  obtain ⟨base,hY,hZ⟩ := exists_small_projection_data F N R hF p q hFp hNq
    c hdeg hmix
  have he (g : ↥(activeFactors F N)) :
      Nonempty (AdaptiveUnitProjectionFamily (base g) (exactFlag g.1) q) := by
    have hg := activeFactors_spec F N g
    exact exists_adaptiveUnitProjectionFamily_of_nested (exactFlag g.1) q
      (base g) (hY g) (hZ g) hg.2.2.2 hg.1 hg.2.2.1
      ((support_subset_flagSupport_iff _ _).mpr (polynomialIn_exactFlag g.1))
      ((support_subset_flagSupport_iff _ _).mpr hNq)
  exact ⟨⟨base, fun g => (Classical.choice (he g)).toAdaptiveUnitPoleBudget⟩⟩

/-- Pure-flag aggregation keeps the original cumulative factor inequalities. -/
theorem sum_cost_le (F N R : Poly) (p q r : FlagDegree)
    (hF : F ≠ 0) (hFp : PolynomialInFlag p F) (B : SliceBudgets F N R q) :
    (∑ g : ↥(activeFactors F N), ∑ C : RegularComponent E g.1 N R,
      (B.unit g).toPrimeFlagBudgetFamily.weightedCost r C) ≤ flagMixed p q r :=
  PureFlagSliceBudget6807.all_active_slice_costs_le F N R hF p q r hFp B.base B.unit

end
end ProximityPrize.SubmissionLower.SmallSliceBudgets6807


