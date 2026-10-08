-- Prove2me | Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Coins
-- name    : RobbinsSeqDesign_StayOrSwitch_Coins
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:32.238842+00:00
-- url     : https://prove2.me/theorems/773ce01b-b44f-4c91-a2aa-a5d12d1dd3a8
-- title:
--   The two coins of Section 2 as a two-armed bandit, and γ = (α+β)/2, δ = |α−β|/2 of (5)
-- statement:
--   Two coins $A$ and $B$ have unknown head probabilities $\alpha$ and $\beta$ with $0 \le \alpha, \beta \le 1$. A toss pays $\$1$ for heads and nothing for tails, so the payoff $x$ of one toss of a coin with head probability $a$ has the law
--
--   $$
--   \mathcal L_a = (1-a)\,\delta_0 + a\,\delta_1 \quad\text{on } \mathbb R .
--   $$
--
--   The pair of coins is the two-armed stochastic bandit whose arm $0$ is coin $A$ (law $\mathcal L_\alpha$) and whose arm $1$ is coin $B$ (law $\mathcal L_\beta$); the mean payoff of each arm is its head probability. The file also defines the two parameters of Eq. (5),
--
--   $$
--   \gamma = \frac{\alpha+\beta}{2}, \qquad \delta = \frac{|\alpha-\beta|}{2},
--   $$
--
--   so that $\max(\alpha,\beta) = \gamma + \delta$.
--
--   These are the objects of Robbins' coin example: every statement of the mission is about this bandit.
--
--   **Formalization Note** The head probabilities are elements of `unitInterval` ($[0,1]$ as a subtype of $\mathbb R$). The bandit is the published `BanditAlgorithm.StochasticBandit 2`; heads is the payoff value $1$. `gamma` and `delta` are defined for all real $\alpha, \beta$.
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), p. 529, Section 2 (coins, x_i, α, β) and p. 531, Eq. (5)

import Mathlib
import Definitions.Def_StochasticBandit

/-!
Robbins, *Some aspects of the sequential design of experiments*,
Bull. Amer. Math. Soc. 58 (1952), Section 2, pp. 529–531.

Two coins `A` (arm `0`) and `B` (arm `1`) with head probabilities `α, β ∈ [0, 1]`; a head pays
`$1` (reward `1`), a tail pays nothing (reward `0`). The quantities `γ = (α + β)/2` and
`δ = |α − β|/2` of Eq. (5).
-/

open MeasureTheory ProbabilityTheory

namespace RobbinsSeqDesign.StayOrSwitch

/-- The law on `ℝ` of the payoff of one toss of a coin with head probability `a`:
`(1 − a) δ₀ + a δ₁` (`1` = heads, `0` = tails). -/
noncomputable def coinLaw (a : unitInterval) : Measure ℝ :=
  ENNReal.ofReal (1 - (a : ℝ)) • Measure.dirac 0 + ENNReal.ofReal (a : ℝ) • Measure.dirac 1

instance coinLaw.instIsProbabilityMeasure (a : unitInterval) :
    IsProbabilityMeasure (coinLaw a) := by
  constructor
  have h0 : (0 : ℝ) ≤ (a : ℝ) := a.2.1
  have h1 : (a : ℝ) ≤ 1 := a.2.2
  simp only [coinLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) h0]
  simp

/-- The two-coin bandit of Section 2 (p. 529): arm `0` is coin `A` with head probability `α`,
arm `1` is coin `B` with head probability `β`; the reward of a toss is `1` for heads and `0`
for tails. -/
noncomputable def coins (α β : unitInterval) : BanditAlgorithm.StochasticBandit 2 where
  P := fun i => if i = 0 then coinLaw α else coinLaw β
  prob := fun i => by
    by_cases h : i = 0 <;> simp only [h, if_true, if_false] <;> infer_instance

/-- `γ = (α + β)/2`, Eq. (5). -/
noncomputable def gamma (α β : ℝ) : ℝ := (α + β) / 2

/-- `δ = |α − β|/2`, Eq. (5). -/
noncomputable def delta (α β : ℝ) : ℝ := |α - β| / 2

end RobbinsSeqDesign.StayOrSwitch


