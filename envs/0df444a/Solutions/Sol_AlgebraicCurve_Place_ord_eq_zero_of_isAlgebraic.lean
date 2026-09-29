-- Prove2me | solution 1 for AlgebraicCurve.Place.ord_eq_zero_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/591dca2e-9d30-57f7-ba51-3a096f58cf96

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.RingTheory.Algebraic.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic

noncomputable section
open Polynomial

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.mem_of_eval_monic_eq_zero Place"
namespace Place
p2m_export "AlgebraicCurve.Place" "mem_of_eval_monic_eq_zero ext ord ord_zero ord_coe_unit algebraMap_mem' toValuationSubring"
namespace FF2R0
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F)

private theorem mem_of_isAlgebraic {x : F} (hx : IsAlgebraic K x) : x ∈ v.toValuationSubring := by
  have hint : IsIntegral K x := hx.isIntegral
  refine v.mem_of_eval_monic_eq_zero (P := (minpoly K x).map (algebraMap K F)) ((minpoly.monic hint).map _)
    (fun i => ?_) ?_
  · rw [coeff_map]; exact v.algebraMap_mem' _
  · rw [eval_map_algebraMap, minpoly.aeval]

theorem ord_eq_zero_of_isAlgebraic' {x : F} (hx : IsAlgebraic K x) : v.ord x = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0, v.ord_zero]
  · let u : v.toValuationSubringˣ :=
      { val := ⟨x, mem_of_isAlgebraic v hx⟩
        inv := ⟨x⁻¹, mem_of_isAlgebraic v hx.inv⟩
        val_inv := Subtype.ext (mul_inv_cancel₀ hx0)
        inv_val := Subtype.ext (inv_mul_cancel₀ hx0) }
    exact v.ord_coe_unit u

end AlgebraicCurve.Place.FF2R0

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {x : F} (hx : IsAlgebraic K x) :
    v.ord x = 0 :=
  AlgebraicCurve.Place.FF2R0.ord_eq_zero_of_isAlgebraic' v hx

end

end S_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic (solution)
