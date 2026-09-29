-- Prove2me | solution 1 for AlgebraicCurve.CellDissection.euler_count_grid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8f2a0a26-19cf-56b3-903d-860f50622951

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CellDissection_euler_count_grid

set_option autoImplicit false

namespace EulerGridCount

theorem euler_count_grid (n J K np nc : ℕ) (g : ℤ) (hJK : np + nc = J * K)
    (ιc : Type*) [Fintype ιc] (hnc : Fintype.card ιc = nc)
    (fib : ιc → Type*) [∀ b, Fintype (fib b)] (ec : ∀ b, fib b → ℕ)
    (hec : ∀ b, ∑ w, ec b w = n)
    (ιp : Type*) [Fintype ιp] (ep : ιp → ℕ) (hep : ∑ q, ep q = n)
    (hRH : (∑ b, ∑ w, ((ec b w : ℤ) - 1)) + ∑ q, ((ep q : ℤ) - 1) = 2 * g - 2 + 2 * (n : ℤ)) :
    2 * ((n : ℤ) * ((J + 1) * (K + 1) + J * K + K)) -
        ((6 * n * np : ℤ) + (∑ b, ∑ w, (6 * ec b w : ℤ)) + ∑ q, ((ep q : ℤ) * (2 * J + 4 * K))) +
        2 * ((n * np : ℤ) + (∑ b, (Fintype.card (fib b) : ℤ)) + Fintype.card ιp) =
      2 * (2 - 2 * g) := by

  have hcap' : ∀ b : ιc, (∑ w, ((ec b w : ℤ) - 1)) = (n : ℤ) - Fintype.card (fib b) := by
    intro b
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum, hec b]; simp

  have hinf' : (∑ q, ((ep q : ℤ) - 1)) = (n : ℤ) - Fintype.card ιp := by
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum, hep]; simp

  have hS : (∑ b, ∑ w, ((ec b w : ℤ) - 1)) = (nc : ℤ) * n - ∑ b, (Fintype.card (fib b) : ℤ) := by
    simp only [hcap']; rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hnc]; simp

  have h6 : (∑ b, ∑ w, (6 * ec b w : ℤ)) = 6 * (n : ℤ) * nc := by
    have h6n : (∑ b, ∑ w, 6 * ec b w) = 6 * n * nc := by
      simp only [← Finset.mul_sum, hec, Finset.sum_const, Finset.card_univ, hnc, smul_eq_mul]; ring1
    exact_mod_cast h6n

  have hp : (∑ q, ((ep q : ℤ) * (2 * J + 4 * K))) = (n : ℤ) * (2 * J + 4 * K) := by
    rw [← Finset.sum_mul, ← Nat.cast_sum, hep]

  have hJK' : (np : ℤ) + nc = J * K := by
    exact_mod_cast hJK

  linear_combination (-4 * (n : ℤ)) * hJK' - 2 * hRH - h6 - hp + 2 * hS + 2 * hinf'

end EulerGridCount

theorem solution (n J K np nc : ℕ) (g : ℤ) (hJK : np + nc = J * K)
    (ιc : Type*) [Fintype ιc] (hnc : Fintype.card ιc = nc)
    (fib : ιc → Type*) [∀ b, Fintype (fib b)] (ec : ∀ b, fib b → ℕ)
    (hec : ∀ b, ∑ w, ec b w = n)
    (ιp : Type*) [Fintype ιp] (ep : ιp → ℕ) (hep : ∑ q, ep q = n)
    (hRH : (∑ b, ∑ w, ((ec b w : ℤ) - 1)) + ∑ q, ((ep q : ℤ) - 1) = 2 * g - 2 + 2 * (n : ℤ)) :
    2 * ((n : ℤ) * ((J + 1) * (K + 1) + J * K + K)) -
        ((6 * n * np : ℤ) + (∑ b, ∑ w, (6 * ec b w : ℤ)) + ∑ q, ((ep q : ℤ) * (2 * J + 4 * K))) +
        2 * ((n * np : ℤ) + (∑ b, (Fintype.card (fib b) : ℤ)) + Fintype.card ιp) =
      2 * (2 - 2 * g) := by
  exact EulerGridCount.euler_count_grid (n := n) (J := J) (K := K) (np := np) (nc := nc) (g := g) (hJK := hJK) (ιc := ιc) (hnc := hnc) (fib := fib) (ec := ec) (hec := hec) (ιp := ιp) (ep := ep) (hep := hep) (hRH := hRH)

end S_AlgebraicCurve_CellDissection_euler_count_grid
end P2MW
export P2MW.S_AlgebraicCurve_CellDissection_euler_count_grid (solution)
