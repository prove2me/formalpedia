-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.exists_lt_pow_le_inv_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:11.055037+00:00
-- url     : https://prove2.me/submissions/4905611e-6336-47f9-a02b-d7bc7d8066bc

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent

set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {t ε : ℝ} (ht : 1 < t) {n₀ : ℕ} (hε0 : 0 < ε)
    (hε : ε < (t ^ (n₀ + 1))⁻¹) : ∃ n, n₀ < n ∧ t ^ n ≤ ε⁻¹ ∧ ε⁻¹ < t ^ (n + 1) := by
  have hlt : t ^ (n₀ + 1) < ε⁻¹ := (lt_inv_comm₀ hε0 (by positivity)).1 hε
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near ((one_le_pow₀ ht.le).trans hlt.le) ht
  exact ⟨n, Nat.succ_lt_succ_iff.1 ((pow_lt_pow_iff_right₀ ht).1 (hlt.trans hn')), hn, hn'⟩
end ArithmeticTriangleRemovalInVectorSpaces
