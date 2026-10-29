-- Prove2me | Definitions.Def_PutermanMDP_SemiMarkov_Model
-- name    : PutermanMDP_SemiMarkov_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:26.073335+00:00
-- url     : https://prove2.me/theorems/c68372aa-c9ac-4eaa-b6ce-27e3c8101e54
-- title:
--   Semi-Markov data and stationary randomized decision rules
-- statement:
--   Let $S$ be a state space and let $A_s$ be a nonempty set of feasible actions at state $s$. An action specifies a next-state probability mass function $m(\cdot\mid s,a)$, a probability law $F(\cdot\mid s,a)$ on nonnegative holding times with a finite first moment, and a real expected one-transition reward $r(s,a)$. Write
--   $$y(s,a)=\int t\,F(dt\mid s,a).$$
--   The joint distribution function is $Q(t,j\mid s,a)=m(j\mid s,a)F(t\mid s,a)$. Assumption 11.1.1 requires positive constants $\varepsilon,\delta$ with $F(\delta\mid s,a)\le1-\varepsilon$ uniformly. A stationary randomized rule $d$ assigns a probability mass function on $A_s$; its reward and holding-time mixtures must be absolutely summable. Its embedded transition law is the corresponding mixture of the next-state distributions.
--
--   This supplies the primitive probability data and the finite real quantities needed for stationary evaluation. It does not assume any evaluation or optimality equation.
--
--   **Formalization Note** Action types depend on the state, so feasibility is built into the domain. Randomization uses discrete probability mass functions, as in the discrete-action stochastic construction of Section 11.1.4. Holding-time laws remain arbitrary probability measures; exponential holding times are not imposed. The source's reward reduction in Section 11.4.1 is used as the primitive reward datum.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, https://doi.org/10.1002/9780470316887, pp. 531–535, 549–550 (PDF 547–551, 565–566), Eqs. (11.1.1)–(11.1.3), (11.4.5)–(11.4.9)

import Mathlib

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PutermanMDP.SemiMarkov

/-- Decision-epoch data; feasible actions have their own nonempty type at each state.
The holding-time law is arbitrary, not necessarily exponential. -/
structure Model (S : Type*) where
  Action : S → Type
  action_nonempty : ∀ s, Nonempty (Action s)
  transition : (s : S) → Action s → PMF S
  holding : (s : S) → Action s → Measure ℝ≥0
  holding_probability : ∀ s a, IsProbabilityMeasure (holding s a)
  holding_integrable : ∀ s a, Integrable (fun t : ℝ≥0 => (t : ℝ)) (holding s a)
  reward : (s : S) → Action s → ℝ

variable {S : Type*}

noncomputable def meanTime (M : Model S) (s : S) (a : M.Action s) : ℝ :=
  ∫ t : ℝ≥0, (t : ℝ) ∂M.holding s a

/-- Assumption 11.1.1: uniform positive tail at a positive duration. -/
def Nonexplosive (M : Model S) : Prop :=
  ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
    ∀ s a, M.holding s a {t | (t : ℝ) ≤ δ} ≤ ENNReal.ofReal (1 - ε) ∧ ε ≤ 1

/-- The semi-Markov kernel of (11.1.2), with independent next state and sojourn
conditional on the present state and action. -/
noncomputable def jointCDF (M : Model S) (t : ℝ) (j s : S) (a : M.Action s) : ℝ≥0∞ :=
  M.transition s a j * M.holding s a {u | (u : ℝ) ≤ t}

/-- A stationary randomized decision rule. Absolute summability spells out that
its expected one-transition reward and mean holding time are finite real numbers. -/
structure Rule (M : Model S) where
  action : (s : S) → PMF (M.Action s)
  reward_summable : ∀ s, Summable (fun a => (action s a).toReal * M.reward s a)
  time_summable : ∀ s, Summable (fun a => (action s a).toReal * meanTime M s a)

noncomputable def ruleReward (M : Model S) (d : Rule M) (s : S) : ℝ :=
  ∑' a, (d.action s a).toReal * M.reward s a

noncomputable def ruleTime (M : Model S) (d : Rule M) (s : S) : ℝ :=
  ∑' a, (d.action s a).toReal * meanTime M s a

noncomputable def embedded (M : Model S) (d : Rule M) (s : S) : PMF S :=
  (d.action s).bind (M.transition s)

end PutermanMDP.SemiMarkov


