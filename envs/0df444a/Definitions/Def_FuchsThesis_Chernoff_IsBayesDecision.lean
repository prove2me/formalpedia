-- Prove2me | Definitions.Def_FuchsThesis_Chernoff_IsBayesDecision
-- name    : FuchsThesis_Chernoff_IsBayesDecision
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:15.612445+00:00
-- url     : https://prove2.me/theorems/f4d4d3b1-8536-4d00-9c1e-ace4ccbe6bb8
-- title:
--   Bayes' decision function $\delta_B$, eq. (2.6)
-- statement:
--   With priors $\pi_0, \pi_1$ and distributions $p_0, p_1$ on a finite outcome set, **Bayes' decision function** guesses the hypothesis with the larger posterior probability:
--
--   $$
--   \delta_B(b) = \begin{cases} 0 & \text{if } \pi_0 p_0(b) > \pi_1 p_1(b),\\ 1 & \text{if } \pi_1 p_1(b) > \pi_0 p_0(b),\\ \text{anything} & \text{if } \pi_0 p_0(b) = \pi_1 p_1(b). \end{cases}
--   $$
--
--   Because the value on ties is free, this is a property of a decision function $\delta$: $\delta$ is a Bayes decision function when it makes the prescribed choice at every outcome $b$ with $\pi_0 p_0(b) \neq \pi_1 p_1(b)$.
--
--   **Formalization Note** A predicate on maps $\delta$ from the outcome type to $\mathrm{Fin}\,2$; ties are left unconstrained, so every tie-breaking rule is covered.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.2.1, eq. (2.6), p.14 (PDF p.23)

import Mathlib

namespace FuchsThesis.Chernoff

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §2.2.1, eq. (2.6), p.14 (PDF p.23).

Bayes' decision function: `δB(b) = 0` if `π0 p0(b) > π1 p1(b)`, `δB(b) = 1` if
`π1 p1(b) > π0 p0(b)`, and "anything" if `π0 p0(b) = π1 p1(b)`.

**Formalization Note.** Because the source leaves the choice on ties free, "Bayes' decision
function" is a predicate on decision functions `δ : B → Fin 2`: it fixes `δ(b)` exactly at the
outcomes where `π0 p0(b) ≠ π1 p1(b)` and leaves it unconstrained at ties. -/
def IsBayesDecision {B : Type} (π0 π1 : ℝ) (p0 p1 : B → ℝ) (δ : B → Fin 2) : Prop :=
  ∀ b, (π1 * p1 b < π0 * p0 b → δ b = 0) ∧ (π0 * p0 b < π1 * p1 b → δ b = 1)

end FuchsThesis.Chernoff


