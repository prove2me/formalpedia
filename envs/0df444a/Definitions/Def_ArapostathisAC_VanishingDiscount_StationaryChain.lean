-- Prove2me | Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain
-- name    : ArapostathisAC_VanishingDiscount_StationaryChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T07:16:52.032537+00:00
-- url     : https://prove2.me/theorems/d2fd36c6-e369-4e00-bd45-eb197da14714
-- title:
--   Irreducibility and positive recurrence of the state chain of a stationary policy
-- statement:
--   Let $f\in\Pi_{SD}$ be a stationary deterministic policy of the countable-state controlled Markov process of §5. Under $f$ the state process $\{X_t\}$ is a Markov chain on $S=\{0,1,2,\dots\}$ with transition probabilities $P(j\mid i,f(i))$. For a state $i$ let
--   $$\tau_i=\min\{t\ge 1: X_t=i\}\qquad(\tau_i=\infty\text{ if there is no such }t)$$
--   be the first return time to $i$.
--
--   1. The chain is **irreducible** if for all $i,j\in S$ there is $n\ge 0$ with $P^f_i(X_n=j)>0$.
--   2. The chain is **positive recurrent** if $E^f_i[\tau_i]<\infty$ for every $i\in S$.
--
--   These are the hypotheses of the converse part of Theorem 5.1.
--
--   **Formalization Note.** Probabilities and expectations are taken under the path measure $P^f_i$ of the policy $f$; the expected return time is a lower Lebesgue integral of the $[0,\infty]$-valued return time. Positive recurrence is required of every state; for an irreducible chain this is equivalent to positive recurrence of one state.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 299, Theorem 5.1 ("the corresponding chain is irreducible and positive recurrent")

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ArapostathisAC.VanishingDiscount

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- The first return time `τ_i(ω) = min {t ≥ 1 : X_t = i}` of a trajectory to the state `i`,
equal to `⊤` when the trajectory never returns. -/
noncomputable def returnTime (i : ℕ) (ω : ℕ → ℕ × A) : ℕ∞ :=
  ⨅ t : {t : ℕ // 1 ≤ t ∧ (ω t).1 = i}, (t.1 : ℕ∞)

/-- The state chain of `f ∈ Π_SD` is irreducible: from every state `i`, every state `j` is reached
with positive probability at some time `n`. -/
def IsIrreducible (M : CMP A) (f : StationaryPolicy M) : Prop :=
  ∀ i j, ∃ n : ℕ, 0 < pathMeasure M f.toPolicy i {ω | (ω n).1 = j}

/-- The state chain of `f ∈ Π_SD` is positive recurrent: started at any state `i`, the expected
return time to `i` is finite. -/
def IsPositiveRecurrent (M : CMP A) (f : StationaryPolicy M) : Prop :=
  ∀ i, ∫⁻ ω, ((returnTime i ω : ℕ∞) : ℝ≥0∞) ∂(pathMeasure M f.toPolicy i) ≠ ⊤

end ArapostathisAC.VanishingDiscount


