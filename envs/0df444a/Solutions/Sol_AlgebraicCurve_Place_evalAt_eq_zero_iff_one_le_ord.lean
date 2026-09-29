-- Prove2me | solution 1 for AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a03adaa6-82fe-577c-9b42-6bfb0b6018d4

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_ModPFormFn
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_mk_mem_maximalIdeal_iff
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

namespace FltWs24
namespace KerX

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_eq_zero_iff_one_le_ord (x : Place K F) (hx : x.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ x.toValuationSubring) : x.evalAt f = 0 ↔ 1 ≤ x.ord f := by
  constructor
  · intro h0
    by_contra hlt
    have hnn : 0 ≤ x.ord f := (Place.mem_iff_ord_nonneg x hf0).mp hf
    exact Place.evalAt_ne_zero x hx hf0 (by omega) h0
  · intro h1
    have hmem : (⟨f, hf⟩ : x.toValuationSubring) ∈ IsLocalRing.maximalIdeal x.toValuationSubring :=
      (Place.mk_mem_maximalIdeal_iff x hf).mpr (Or.inr (by omega))
    have h := x.algebraMap_evalAt hx hf
    rw [(IsLocalRing.residue_eq_zero_iff _).mpr hmem, map_eq_zero] at h
    exact h

theorem evalAt_zpow_mul_eq_zero_iff_one_le_stackOrd [DecidableEq K] (N : ℕ) [NeZero N]
    (x : Place K ↥(modularFunctionFieldC K N)) (hx : x.IsRational) (m a : ℤ)
    (hu : 1 ≤ placeWidth N x)
    (ha : (placeWidth N x : ℤ) * a = m * ((jWidth (x.evalAt (jGeomGen K N)) : ℤ) - 1))
    (π : ↥(modularFunctionFieldC K N)) (hπ : x.ord π = 1)
    (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0) (hG : -a ≤ x.ord G) :
    x.evalAt (π ^ a * G) = 0 ↔ 1 ≤ stackOrd N m G x := by
  have hπ0 : π ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hπ; exact zero_ne_one hπ
  have hf0 : π ^ a * G ≠ 0 := mul_ne_zero (zpow_ne_zero a hπ0) hG0
  have hord : x.ord (π ^ a * G) = a + x.ord G := by
    rw [x.ord_mul (zpow_ne_zero a hπ0) hG0, Place.ord_zpow, hπ, mul_one]
  have hmem : π ^ a * G ∈ x.toValuationSubring :=
    (Place.mem_iff_ord_nonneg x hf0).mpr (by rw [hord]; omega)
  rw [evalAt_eq_zero_iff_one_le_ord x hx hf0 hmem, hord]
  unfold stackOrd
  rw [← ha, ← mul_add]

  have hu1 : (1 : ℤ) ≤ (placeWidth N x : ℤ) := by exact_mod_cast hu
  set u : ℤ := (placeWidth N x : ℤ) with hudef
  constructor
  · intro h; nlinarith
  · intro h
    by_contra hlt
    have : x.ord G + a ≤ 0 := by omega
    nlinarith

end FltWs24.KerX

open FltWs24.KerX in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : Place K F) (hx : x.IsRational) {f : F} (hf0 : f ≠ 0) (hf : f ∈ x.toValuationSubring) :
    x.evalAt f = 0 ↔ 1 ≤ x.ord f := evalAt_eq_zero_iff_one_le_ord x hx hf0 hf

end S_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
end P2MW
export P2MW.S_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord (solution)
