-- Prove2me | Definitions.Def_CommodityCPC_BayesianGame
-- name    : CommodityCPC_BayesianGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:50:03.590817+00:00
-- url     : https://prove2.me/theorems/ebff0186-d244-410e-afdb-7c90bde72513
-- title:
--   Bayesian game with real signals and real actions: admissible strategies, ex ante payoff, Bayesian Nash equilibrium
-- statement:
--   A **Bayesian game** with real private signals and real actions consists of a set $I$ of players, a prior $P$ on a measurable space of states $\Omega$, a signal $f_i:\Omega\to\mathbb R$ for each player, and a payoff $u_i(x,\omega)$ of player $i$ at the action profile $x\in\mathbb R^I$ in the state $\omega$.
--
--   A strategy of player $i$ is a function $q:\mathbb R\to\mathbb R$ applied to the player's own signal. It is **admissible** if it is measurable and $q(f_i)$ is square integrable under $P$. At a strategy profile $\sigma$, the realized payoff of player $i$ is $u_i\big((\sigma_k(f_k))_k,\omega\big)$, and the **ex ante payoff** is its expectation under $P$.
--
--   A profile $\sigma$ is a **Bayesian Nash equilibrium** if every $\sigma_i$ is admissible and, for every player $i$ and every admissible $g$,
--
--   $$
--   E\big[u_i(g,\sigma_{-i})\big]\le E\big[u_i(\sigma)\big].
--   $$
--
--   This is a general object, independent of the procurement model, and it is the equilibrium notion of the whole mission. The deviations range over all admissible strategies, not only over affine ones.
--
--   **Formalization Note** Actions are unrestricted in sign. For square-integrable strategies the ex ante condition is equivalent, up to null sets, to the interim condition that each player maximizes the conditional expected payoff given the signal.
-- source:
--   Xing–Liu–Zhang–Zhao, SSRN 4717149 (2023-12-27), §3, pp. 9–10; version of record: Management Science (2024), doi:10.1287/mnsc.2023.00304

import Mathlib

namespace CommodityCPC

open MeasureTheory

noncomputable section

/-- **A Bayesian game with real private signals and real actions.** A general object, on which the
Cournot model of Xing–Liu–Zhang–Zhao, *The Bright Side of Price Volatility in Global Commodity
Procurement*, SSRN 4717149 (2023-12-27), Management Science (2024), doi:10.1287/mnsc.2023.00304,
§3, pp. 9–10, is built. Nature draws a state `ω` from `P`; player `i` observes `signal i ω` and
chooses an action in `ℝ`; `payoff i x ω` is player `i`'s payoff at the action profile `x` in
state `ω`.

**Formalization Note.** Actions are unrestricted in sign. -/
structure BayesianGame (I Ω : Type*) [MeasurableSpace Ω] where
  /-- The common prior on the states. -/
  P : Measure Ω
  /-- The private signal of each player. -/
  signal : I → Ω → ℝ
  /-- `payoff i x ω`: the payoff of player `i` at the action profile `x` in the state `ω`. -/
  payoff : I → (I → ℝ) → Ω → ℝ

namespace BayesianGame

variable {I Ω : Type*} [MeasurableSpace Ω] (G : BayesianGame I Ω)

/-- A strategy `q : ℝ → ℝ` of player `i`, applied to the player's own signal, is **admissible** if
it is measurable and the resulting action is square integrable under the prior.

**Formalization Note.** Square integrability is what makes the ex ante payoff of a quadratic
game a genuine (finite) expectation, see `CommodityCPC.Params.game`. -/
def Admissible (i : I) (q : ℝ → ℝ) : Prop :=
  Measurable q ∧ MemLp (fun ω => q (G.signal i ω)) 2 G.P

/-- The payoff of player `i` in the state `ω` when every player `k` follows the strategy `σ k`
on their own signal. -/
def realizedPayoff (i : I) (σ : I → ℝ → ℝ) (ω : Ω) : ℝ :=
  G.payoff i (fun k => σ k (G.signal k ω)) ω

/-- The ex ante expected payoff of player `i` at the strategy profile `σ`. -/
def exAntePayoff (i : I) (σ : I → ℝ → ℝ) : ℝ :=
  ∫ ω, G.realizedPayoff i σ ω ∂G.P

/-- **Bayesian Nash equilibrium**: every strategy of the profile is admissible, and no player can
raise their ex ante expected payoff by a unilateral deviation to *any* admissible strategy.

**Formalization Note.** This is the ex ante form of the interim condition "firm `i` solves
`max_{q_i} E[π_i | f_i]`" of Xing et al., p. 10: a profile of square-integrable strategies is
optimal ex ante among square-integrable strategies iff it is optimal given the signal up to
null sets. -/
def IsBNE [DecidableEq I] (σ : I → ℝ → ℝ) : Prop :=
  (∀ i, G.Admissible i (σ i)) ∧
    ∀ i g, G.Admissible i g →
      G.exAntePayoff i (Function.update σ i g) ≤ G.exAntePayoff i σ

end BayesianGame

end

end CommodityCPC


