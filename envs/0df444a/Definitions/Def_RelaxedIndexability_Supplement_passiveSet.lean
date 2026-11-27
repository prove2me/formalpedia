-- Prove2me | Definitions.Def_RelaxedIndexability_Supplement_passiveSet
-- name    : RelaxedIndexability_Supplement_passiveSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:01:22.185838+00:00
-- url     : https://prove2.me/theorems/b3bc1dec-07a8-5f0f-8f08-2794f199be33
-- title:
--   Passive set $P(m)$ of the single-armed bandit with subsidy
-- statement:
--   For one arm, a discount factor $\beta$ and a subsidy $m$, the **passive set** is the set of beliefs at which the passive action is optimal, ties included:
--
--   $$
--   P(m)=\{\omega\in\mathbb X:\ V_{\beta,m}(\omega;u=1)\le V_{\beta,m}(\omega;u=0)\},
--   $$
--
--   where $\mathbb X$ is the belief simplex and $V_{\beta,m}(\omega;u)$ are the optimal action values (13)–(14).
--
--   The passive set is the object whose monotonicity in $m$ is classical indexability (Definition 1).
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, (15), p.11

import Mathlib
import Definitions.Def_RelaxedIndexability_Supplement_optimalValue

namespace RelaxedIndexability.Supplement

variable {K : ℕ}

/-- **The passive set `P(m) = {ω : V_{β,m}(ω; u = 1) ≤ V_{β,m}(ω; u = 0)}`**
(Liu, arXiv:2107.11939v4, (15), p.11): the beliefs at which the passive action is optimal, ties
included.

**Formalization Note.** A subset of the belief simplex, defined with the optimal action values. -/
def passiveSet (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B : Fin K → ℝ) (m : ℝ) :
    Set (Fin K → ℝ) :=
  {ω | ω ∈ stdSimplex ℝ (Fin K) ∧
    optimalActionValue β P B m true ω ≤ optimalActionValue β P B m false ω}

end RelaxedIndexability.Supplement


