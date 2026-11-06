-- Prove2me | Definitions.Def_HMajConsensus_IsGood
-- name    : HMajConsensus_IsGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:43.614939+00:00
-- url     : https://prove2.me/theorems/36c29435-a3a7-4845-a977-fc26842d7e8d
-- title:
--   Gap $\Delta$, growth rate $\gamma=\min\{h^2p_1,1\}$, good configurations $(\star)$ and successful phases
-- statement:
--   Fix a reference opinion $i_0$ (the paper's "opinion 1" of §6, which does not sort the other opinions). For a configuration $C$ with densities $p_i=p_i(C)$ define the gaps
--   $$\Delta_i=p_{i_0}-p_i,\qquad \Delta=\min_{i\ne i_0}\Delta_i,$$
--   and the **growth-rate parameter** $\gamma=\min\{h^2p_{i_0},1\}$. For a constant $K>0$, the configuration is **good** if $p_{i_0}>0$ and
--   $$\Delta\ \ge\ K\sqrt{\frac{p_{i_0}}{\gamma}\cdot\frac{\ln n}{n}}.\tag{$\star$}$$
--   The **phase** started at a configuration $C(0)$ **succeeds** at a configuration $C$ when either $p_{i_0}(C)\ge 3/5$, or $p_{i_0}(C)\ge 2p_{i_0}(C(0))$, $\Delta(C)\ge p_{i_0}(C)/32$ and $C$ is good with the same constant $K$.
--
--   These notions organize the plurality-consensus argument of §6: a good configuration is one in which opinion $i_0$ has broken symmetry, and an amplification phase ends when the density of $i_0$ has doubled while staying good, or has reached $3/5$.
--
--   **Formalization Note** $K$ is the paper's absolute constant $C$ of (⋆), made a parameter; statements quantify it as the paper does. $\ln$ is `Real.log`. The minimum is the real infimum over the finite set $\{i\ne i_0\}$, nonempty under the mission's standing hypothesis $k\ge2$.
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, §6, pp.28–29 (∆_i, ∆, γ, good configuration (⋆)); §6.2, p.30 (success of a phase)

import Mathlib
import Definitions.Def_HMajConsensus_pathLaw

namespace HMajConsensus

/-- The gap `∆(C) = min_{i ≠ i₀} (p_{i₀} − p_i)` between the reference opinion `i₀` (the paper's
"opinion 1") and every other opinion (d'Amore, Rybicki, Shimizu, Shiraga, Vacus,
arXiv:2610.40562, §6, p.28: `∆_i(t) := p_1(t) − p_i(t)` and `∆(t) := min_{i>1} ∆_i(t)`).

**Formalization Note** §6 does not sort the opinions; "opinion 1" is the label `i₀`. The minimum
is the real infimum over the finite set `{i ≠ i₀}`, which is nonempty under the mission's
standing hypothesis `2 ≤ k` (for `k = 1` the value would be the default `0`). -/
noncomputable def gapMin {n k : ℕ} (C : Config n k) (i₀ : Fin k) : ℝ :=
  ⨅ i : {i : Fin k // i ≠ i₀}, (density C i₀ - density C i)

/-- The growth-rate parameter `γ = min{h² p_{i₀}, 1}` (arXiv:2610.40562, §6, p.29). -/
noncomputable def growthRate {n k : ℕ} (h : ℕ) (C : Config n k) (i₀ : Fin k) : ℝ :=
  min ((h : ℝ) ^ 2 * density C i₀) 1

/-- A **good** configuration (arXiv:2610.40562, §6, p.29, condition (⋆)): `p_{i₀} > 0` and
`∆ ≥ C √(p_{i₀}/γ · ln n / n)`, for the absolute constant `C` of §6 (the parameter `K`).

**Formalization Note** `ln` is `Real.log`; `n` is the number of nodes (the length of the
configuration). The constant is a parameter; the statements using it quantify it as §6 does. -/
def IsGood {n k : ℕ} (K : ℝ) (h : ℕ) (C : Config n k) (i₀ : Fin k) : Prop :=
  0 < density C i₀ ∧
    K * Real.sqrt (density C i₀ / growthRate h C i₀ * (Real.log n / n)) ≤ gapMin C i₀

/-- The phase started at round 0 (configuration `C₀`) **succeeds** at a configuration `C`
(arXiv:2610.40562, §6.2, p.30) when either `p_{i₀}(C) ≥ 3/5`, or `p_{i₀}(C) ≥ 2 p_{i₀}(C₀)`,
`∆(C) ≥ p_{i₀}(C)/32` and `C` is good (⋆) with the same constant `K`. -/
def PhaseSucceeds {n k : ℕ} (K : ℝ) (h : ℕ) (C₀ C : Config n k) (i₀ : Fin k) : Prop :=
  3 / 5 ≤ density C i₀ ∨
    (2 * density C₀ i₀ ≤ density C i₀ ∧ density C i₀ / 32 ≤ gapMin C i₀ ∧ IsGood K h C i₀)

end HMajConsensus


