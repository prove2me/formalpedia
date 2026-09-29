-- Prove2me | solution 1 for AlgebraicCurve.Annulus.valuation_evalAt_param_sub_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6bd7a99d-14a8-5f14-8fc9-ee58e8cbdd3c

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_valuation_evalAt_param_sub_algebraMap

set_option autoImplicit false

open AlgebraicCurve IsLocalRing AlgebraicCurve.RationalFunctionField

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F) (P : Place L F) (hP : P ∈ An.dom) (a : L) :
    (A.valuation (P.evalAt An.param) ≠ A.valuation a →
        A.valuation (P.evalAt (An.param - algebraMap L F a)) =
          max (A.valuation (P.evalAt An.param)) (A.valuation a)) ∧
      (A.valuation (P.evalAt An.param) = A.valuation a →
        A.valuation (P.evalAt (An.param - algebraMap L F a)) ≤ A.valuation a ∧
          (a ≠ 0 → ∀ h : a⁻¹ * P.evalAt An.param ∈ A,
            (A.valuation (P.evalAt (An.param - algebraMap L F a)) = A.valuation a ↔
              IsLocalRing.residue A ⟨a⁻¹ * P.evalAt An.param, h⟩ ≠ 1))) := by
  classical
  obtain ⟨hrat, hzmem, ⟨hbA, hbmax⟩, hb0, -⟩ := An.mem_dom P hP
  have hev : P.evalAt (An.param - algebraMap L F a) = P.evalAt An.param - a := by
    rw [AlgebraicCurve.GaussReduction.evalAt_sub_of_mem P hrat hzmem (P.algebraMap_mem' a),
      AlgebraicCurve.GaussReduction.evalAt_algebraMap_const P hrat a]
  rw [hev]
  set b : L := P.evalAt An.param with hb
  refine ⟨fun hne => ?_, fun heq => ⟨?_, ?_⟩⟩
  ·
    have hne' : A.valuation b ≠ A.valuation (-a) := by rwa [Valuation.map_neg]
    rw [sub_eq_add_neg, Valuation.map_add_of_distinct_val _ hne', Valuation.map_neg]
  ·
    calc A.valuation (b - a) ≤ max (A.valuation b) (A.valuation a) := Valuation.map_sub _ _ _
      _ = A.valuation a := by rw [heq, max_self]
  · intro ha0 h
    have hva : A.valuation a ≠ 0 := by
      rwa [ne_eq, Valuation.zero_iff]
    have hfac : b - a = a * (a⁻¹ * b - 1) := by
      field_simp
    have hmul : A.valuation a * A.valuation (a⁻¹ * b - 1) = A.valuation a ↔
        A.valuation (a⁻¹ * b - 1) = 1 := by
      constructor
      · intro h2
        exact mul_left_cancel₀ hva (by rw [h2, mul_one])
      · intro h2
        rw [h2, mul_one]
    rw [hfac, Valuation.map_mul, hmul]

    have hcoe : a⁻¹ * b - 1 = (((⟨a⁻¹ * b, h⟩ : A) - 1 : A) : L) := rfl
    rw [hcoe, ← ValuationSubring.valuation_eq_one_iff, ← IsLocalRing.notMem_maximalIdeal, ne_eq, not_iff_not]
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]

end S_AlgebraicCurve_Annulus_valuation_evalAt_param_sub_algebraMap
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_valuation_evalAt_param_sub_algebraMap (solution)
