-- Prove2me | solution 1 for AlgebraicCurve.Place.transcendental_of_ord_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/67fcf48c-809d-5694-b149-3dcbae67a50d

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.RingTheory.Algebraic.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_transcendental_of_ord_ne_zero

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

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) :
    Transcendental K t :=
  fun h => ht (AlgebraicCurve.Place.FF2R0.ord_eq_zero_of_isAlgebraic' v h)

end

end S_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
end P2MW
export P2MW.S_AlgebraicCurve_Place_transcendental_of_ord_ne_zero (solution)
