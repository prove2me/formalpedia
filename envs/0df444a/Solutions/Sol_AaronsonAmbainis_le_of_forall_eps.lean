-- Prove2me | solution 1 for AaronsonAmbainis.le_of_forall_eps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:18:32.625737+00:00
-- url     : https://prove2.me/submissions/32951f8d-7df6-428a-b7c3-16b8f3fe00a3

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz

set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution {Q S C c : ℝ} (hS : 0 ≤ S) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (h : ∀ ε : ℝ, 0 < ε → Q ≤ S * (C * (S + c * ε))) : Q ≤ C * S ^ 2 := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hK : 0 ≤ C * S * c := mul_nonneg (mul_nonneg hC hS) hc
  have hK1 : 0 < C * S * c + 1 := by linarith
  have h2 := h (δ / (C * S * c + 1)) (div_pos hδ hK1)
  have h3 : C * S * c * (δ / (C * S * c + 1)) ≤ δ := by
    rw [← mul_div_assoc, div_le_iff₀ hK1]
    nlinarith
  calc Q ≤ S * (C * (S + c * (δ / (C * S * c + 1)))) := h2
    _ = C * S ^ 2 + C * S * c * (δ / (C * S * c + 1)) := by ring
    _ ≤ C * S ^ 2 + δ := by linarith
end AaronsonAmbainis
