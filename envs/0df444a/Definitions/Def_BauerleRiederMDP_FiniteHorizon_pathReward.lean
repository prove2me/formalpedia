-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathReward
-- name    : BauerleRiederMDP_FiniteHorizon_pathReward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:10.643188+00:00
-- url     : https://prove2.me/theorems/fe65592f-be53-4c6e-b3a4-5dcee0e42e99
-- title:
--   Total reward of a path
-- statement:
--   For a path whose last $k$ transitions take place at the times $n_0,\dots,n_0+k-1$, with states $x_i$ and actions $a_i$, the total reward is
--
--   $$\sum_{i=n_0}^{n_0+k-1} r_i(x_i,a_i)+g(x_{n_0+k}).$$
--
--   This is the random variable inside the expectations defining $V_{n\pi}$ and, with $r^+$ and $g^+$ in place of $r$ and $g$, $\delta^N_n$.
--
--   **Formalization Note.** The rewards $r$ and $g$ are parameters, so that one definition serves both uses.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.17 and p.18

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History

open MDPFinance.Bellman (Hist histState)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- The total reward of a path: for a path `h = (…, x_{n₀}, a_{n₀}, …, a_{n₀+k-1}, x_{n₀+k})`
whose last `k` transitions happen at the calendar times `n₀, …, n₀+k-1`, the real number
`∑_{i<k} r_{n₀+i}(x_{n₀+i}, a_{n₀+i}) + g(x_{n₀+k})`. This is the random variable inside
`𝔼^π_{nx}` in the definitions of `V_{nπ}` (Bäuerle & Rieder (2011), p.18, PDF 33) and, with `r⁺`
and `g⁺`, of `δ^N_n` (p.17, PDF 32).

**Formalization Note.** `r` and `g` are parameters so that one definition serves both the reward
and its positive part. -/
noncomputable def pathReward {E A : Type u} (r : ℕ → E × A → ℝ) (g : E → ℝ) (n₀ j₀ : ℕ) :
    (k : ℕ) → Hist E A (j₀ + k) → ℝ
  | 0, h => g (histState j₀ h)
  | k + 1, h =>
      let p : Hist E A (j₀ + k) × A × E := h
      pathReward r (fun _ => 0) n₀ j₀ k p.1 + r (n₀ + k) (histState (j₀ + k) p.1, p.2.1) +
        g p.2.2

end BauerleRiederMDP.FiniteHorizon


