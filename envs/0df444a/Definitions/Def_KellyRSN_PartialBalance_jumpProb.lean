-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_jumpProb
-- name    : KellyRSN_PartialBalance_jumpProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:34:51.325181+00:00
-- url     : https://prove2.me/theorems/d729f3e1-3905-49f4-b8fa-1d5610f9c867
-- title:
--   Jump-chain transition probabilities $p(j,k) = q(j,k)/q(j)$
-- statement:
--   For transition rates $q(j,k)$ on a countable state space $\mathcal S$, write $q(j) = \sum_{k \in \mathcal S} q(j,k)$. When the process leaves state $j$ it moves to state $k$ with probability
--   $$
--   p(j,k) = \frac{q(j,k)}{q(j)}, \qquad 0 < q(j) < \infty .
--   $$
--
--   These are the transition probabilities of the jump chain of the Markov process (equation (1.4)). The module also records that every row sums to one.
--
--   **Formalization Note** When $q(j) = 0$ or $q(j) = \infty$ the formula is undefined; the row is then set to "stay at $j$" so that it remains a probability distribution. Under the standing assumptions of the book this case arises only for a one-state space.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 3 (PDF p. 6), §1.1, equation (1.4)

import Mathlib

open scoped ENNReal

namespace KellyRSN.PartialBalance

open Classical in
/-- **Jump-chain transition probabilities.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, §1.1, p. 3 (PDF p. 6), equation (1.4):
"A Markov process remains in state `j` for a length of time which is exponentially distributed
with parameter `q(j) = Σ_{k∈𝒮} q(j, k)`. When it leaves state `j` it moves to state `k` with
probability `p(j, k) = q(j, k) / q(j)` (1.4)."

`jumpProb q j k = q j k / Σ_{k'} q j k'` whenever `0 < q(j) < ∞`.

**Formalization Note.** If `q(j) = 0` (an absorbing state) or `q(j) = ∞` the formula (1.4) is
undefined; the row is then set to "stay at `j`" (`1` if `k = j`, else `0`), so that every row is a
probability distribution (`tsum_jumpProb`). Under the standing assumptions of §1.1
(`IsKellyRates`: `q(j) < ∞`, irreducible) the convention is used only when `S` is a single state. -/
noncomputable def jumpProb {S : Type*} (q : S → S → ℝ≥0∞) (j k : S) : ℝ≥0∞ :=
  if 0 < ∑' k', q j k' ∧ ∑' k', q j k' < ⊤ then q j k / ∑' k', q j k'
  else if k = j then 1 else 0

/-- Every row of `jumpProb q` sums to one (structural lemma used to build the jump-chain kernel). -/
theorem tsum_jumpProb {S : Type*} (q : S → S → ℝ≥0∞) (j : S) : ∑' k, jumpProb q j k = 1 := by
  classical
  by_cases h : 0 < ∑' k', q j k' ∧ ∑' k', q j k' < ⊤
  · simp only [jumpProb, h, and_self, if_true]
    simp_rw [div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_inv_cancel h.1.ne' h.2.ne
  · simp only [jumpProb, h, if_false]
    exact tsum_ite_eq j 1

end KellyRSN.PartialBalance


