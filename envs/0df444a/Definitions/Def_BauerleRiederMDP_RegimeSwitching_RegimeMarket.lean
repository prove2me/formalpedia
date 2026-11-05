-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_RegimeMarket
-- name    : BauerleRiederMDP_RegimeSwitching_RegimeMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:24.149033+00:00
-- url     : https://prove2.me/theorems/3d36faea-8960-450a-ada7-07f2c1895742
-- title:
--   Regime-switching market: environment chain $(p_{jk})$ and return laws $Q_j$
-- statement:
--   A **regime-switching market** is given by
--
--   1. a finite set $E_Y$ of environment states and the transition probabilities $p_{jk}\ge0$, $\sum_k p_{jk}=1$, of the observable environment Markov chain $(Y_n)$;
--   2. for each $j\in E_Y$ the law $Q_j$ of the relative risk $R_{n+1}\in\mathbb R^d$ given $Y_n=j$,
--
--   so that, as in (4.18),
--
--   $$
--   \mathbb P\big(R_{n+1}\in B,\,Y_{n+1}=k\mid Y_n=j,\,R_n\big)=Q_j(B)\,p_{jk}.
--   $$
--
--   $R(j)$ denotes a random vector with law $Q_j$. The environment collects factors (business cycle, policy, catastrophes) that drive the return distribution.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.4, pp.100–101 (PDF pp.114–115), (4.18)

import Mathlib
open MeasureTheory

namespace BauerleRiederMDP.RegimeSwitching

/-- The data of the **regime-switching financial market** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §4.4, pp.100–101, PDF
pp.114–115): a finite set `E_Y` of environment states, the transition probabilities
`p_{jk}` of the observable environment Markov chain `(Y_n)`, and for each `j ∈ E_Y` the law
`Q_j` of the relative risk `R_{n+1} ∈ ℝ^d` given `Y_n = j` (independent of `n`), as in (4.18):
`ℙ(R_{n+1} ∈ B, Y_{n+1} = k | Y_n = j, R_n) = Q_j(B) p_{jk}`.

**Formalization Note.** Only the conditional laws in (4.18) enter the Markov Decision Model, so
the market is given by `(p, Q)`; `R(j)` denotes a random vector with law `Q_j`. The interest
rate `i`, the discount factor `β` and the utilities are parameters of `regimeModel`, and
Assumption (FM) is a hypothesis of each theorem. -/
structure RegimeMarket (EY : Type*) [Fintype EY] (d : ℕ) where
  /-- the transition probabilities `p_{jk}` of the environment chain -/
  p : EY → EY → ℝ
  p_nonneg : ∀ j k, 0 ≤ p j k
  sum_p : ∀ j, ∑ k, p j k = 1
  /-- `Q j = Q_j`, the law of `R(j)` -/
  Q : EY → ProbabilityMeasure (Fin d → ℝ)

end BauerleRiederMDP.RegimeSwitching


