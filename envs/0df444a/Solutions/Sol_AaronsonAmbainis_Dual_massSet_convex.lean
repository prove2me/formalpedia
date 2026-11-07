-- Prove2me | solution 1 for AaronsonAmbainis.Dual.massSet_convex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:38.713205+00:00
-- url     : https://prove2.me/submissions/2bda3a1f-3dcc-4bd4-ace8-d621d56a9779

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (K : ℝ) : Convex ℝ (massSet ι K) := by
  rintro a ⟨ha0, haK⟩ b ⟨hb0, hbK⟩ s r hs hr hsr
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs (ha0 i)) (mul_nonneg hr (hb0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc s * ∑ i, a i + r * ∑ i, b i
        ≤ s * K + r * K :=
          add_le_add (mul_le_mul_of_nonneg_left haK hs) (mul_le_mul_of_nonneg_left hbK hr)
      _ = K := by rw [← add_mul, hsr, one_mul]
end AaronsonAmbainis.Dual
