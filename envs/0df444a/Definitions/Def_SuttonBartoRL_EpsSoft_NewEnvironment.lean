-- Prove2me | Definitions.Def_SuttonBartoRL_EpsSoft_NewEnvironment
-- name    : SuttonBartoRL_EpsSoft_NewEnvironment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:23:15.396132+00:00
-- url     : https://prove2.me/theorems/902eed4d-51c8-4685-a42f-4054ff002046
-- title:
--   The new environment with ε-softness moved inside: p̃(s′, r | s, a) = (1−ε) p(s′, r | s, a) + Σ_{a′} (ε/|A|) p(s′, r | s, a′)
-- statement:
--   Given a finite MDP with a nonempty action set and $0 \le \varepsilon \le 1$, the **new environment** has the same states, actions and rewards, and behaves as follows: in state $s$ with action $a$, with probability $1 - \varepsilon$ it behaves exactly like the original environment, and with probability $\varepsilon$ it repicks the action uniformly at random and behaves like the original environment with the new action. Its dynamics are
--   $$
--   \tilde p(s', r \mid s, a) = (1 - \varepsilon)\, p(s', r \mid s, a) + \sum_{a'} \frac{\varepsilon}{|\mathcal A|}\, p(s', r \mid s, a').
--   $$
--   These are nonnegative and sum to one over $(s', r)$, so the new environment is again a finite MDP.
--
--   The best one can do in the new environment with general policies is the best one can do in the original environment with $\varepsilon$-soft policies; its optimal value function $\tilde v_*$ characterizes the optimal $\varepsilon$-soft policies.
--
--   **Formalization Note** The construction takes the hypotheses $0 \le \varepsilon \le 1$ as arguments (they make $\tilde p$ nonnegative) and requires a nonempty action set (so that $\varepsilon/|\mathcal A|$ is a genuine division). $\tilde v_*$ is the optimal value `optimalValue` of this MDP.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §5.4, p. 102 (the new environment; the altered transition probabilities of the displayed equation for ṽ_*)

import Mathlib
import Definitions.Def_SuttonBartoRL_EpsSoft_MDP

namespace SuttonBartoRL.EpsSoft

variable {S A : Type} [Fintype S] [Fintype A] [Nonempty A]

/-- p. 102: the "new environment" in which the `ε`-softness requirement is moved inside the
environment. It has the same states, actions and rewards as `M`; in state `s` with action `a`, with
probability `1 - ε` it behaves like `M` under `a`, and with probability `ε` it repicks the action
uniformly at random and behaves like `M` under the new action:
`p̃(s', r | s, a) = (1 - ε) p(s', r | s, a) + Σ_{a'} (ε / |A(s)|) p(s', r | s, a')`.
It is an MDP for `0 ≤ ε ≤ 1` and a nonempty action set. -/
noncomputable def epsEnv (M : MDP S A) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : MDP S A where
  R := M.R
  p s a s' r := (1 - ε) * M.p s a s' r + ∑ a', ε / (Fintype.card A : ℝ) * M.p s a' s' r
  p_nonneg s a s' r := by
    have hc : (0 : ℝ) ≤ ε / (Fintype.card A : ℝ) := div_nonneg hε0 (Nat.cast_nonneg _)
    exact add_nonneg (mul_nonneg (by linarith) (M.p_nonneg _ _ _ _))
      (Finset.sum_nonneg fun a' _ => mul_nonneg hc (M.p_nonneg _ _ _ _))
  p_sum s a := by
    have hcard : (Fintype.card A : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := A)).ne'
    simp only [Finset.sum_add_distrib]
    have h1 : ∑ s', ∑ r ∈ M.R, (1 - ε) * M.p s a s' r = 1 - ε := by
      simp_rw [← Finset.mul_sum]
      rw [M.p_sum s a, mul_one]
    rw [h1]
    have h2 : ∑ s', ∑ r ∈ M.R, ∑ a', ε / (Fintype.card A : ℝ) * M.p s a' s' r
        = ∑ a', ε / (Fintype.card A : ℝ) * ∑ s', ∑ r ∈ M.R, M.p s a' s' r := by
      calc ∑ s', ∑ r ∈ M.R, ∑ a', ε / (Fintype.card A : ℝ) * M.p s a' s' r
          = ∑ s', ∑ a', ∑ r ∈ M.R, ε / (Fintype.card A : ℝ) * M.p s a' s' r :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ a', ∑ s', ∑ r ∈ M.R, ε / (Fintype.card A : ℝ) * M.p s a' s' r := Finset.sum_comm
        _ = ∑ a', ε / (Fintype.card A : ℝ) * ∑ s', ∑ r ∈ M.R, M.p s a' s' r := by
            simp_rw [Finset.mul_sum]
    rw [h2]
    simp_rw [M.p_sum s]
    simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring

end SuttonBartoRL.EpsSoft


