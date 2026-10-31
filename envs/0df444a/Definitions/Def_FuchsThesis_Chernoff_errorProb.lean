-- Prove2me | Definitions.Def_FuchsThesis_Chernoff_errorProb
-- name    : FuchsThesis_Chernoff_errorProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:13.990694+00:00
-- url     : https://prove2.me/theorems/b7096d8b-9a96-4f36-b5ef-1ad975280e0b
-- title:
--   Error probability $P_e(\delta)$ of a decision function, eqs. (2.2), (2.3), (2.7)
-- statement:
--   An observer samples once from one of two probability distributions $p_0, p_1$ on a finite outcome set $\{1,\dots,n\}$, the first with prior probability $\pi_0$ and the second with prior probability $\pi_1$. A **decision function** is any map
--
--   $$
--   \delta : \{1,\dots,n\} \to \{0,1\},
--   $$
--
--   the observer's guess of which distribution was sampled, given the outcome $b$. Its **probability of error** is $P_e(\delta) = \pi_0 P(\delta = 1 \mid 0) + \pi_1 P(\delta = 0 \mid 1)$, which is
--
--   $$
--   P_e(\delta) = \pi_0 \sum_{b=1}^{n} \delta(b)\, p_0(b) + \pi_1 \sum_{b=1}^{n} \bigl[1 - \delta(b)\bigr]\, p_1(b).
--   $$
--
--   It is the quantity whose minimum over $\delta$ defines the first distinguishability measure of the thesis.
--
--   **Formalization Note** The outcome set is an arbitrary finite type, the guess lies in $\mathrm{Fin}\,2$, and $\delta(b)$ enters the formula as the real number $0$ or $1$. The definition accepts any real priors and functions; the theorems assume probability vectors and priors $\pi_0,\pi_1 \ge 0$ with $\pi_0 + \pi_1 = 1$.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.2.1, eqs. (2.2), (2.3), (2.7), p.14 (PDF p.23)

import Mathlib

namespace FuchsThesis.Chernoff

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §2.2.1, eqs. (2.2), (2.3) and (2.7), p.14 (PDF p.23).

A decision function `δ : B → {0, 1}` (2.2) guesses, from one sample `b`, which of the two
distributions `p0`, `p1` was sampled. Its probability of error (2.3),
`Pe(δ) = π0 P(δ = 1 | 0) + π1 P(δ = 0 | 1)`, is, as rewritten in (2.7),
`Pe(δ) = π0 ∑_b δ(b) p0(b) + π1 ∑_b [1 − δ(b)] p1(b)`.

**Formalization Note.** The outcome set `{1, …, n}` is an arbitrary finite type `B`; the guess
`{0, 1}` is `Fin 2`, and `δ(b)` enters (2.7) as the real number `0` or `1`. Defined for any real
priors and functions; the theorems assume probability vectors and priors `π0, π1 ≥ 0`,
`π0 + π1 = 1`. -/
noncomputable def errorProb {B : Type} [Fintype B] (π0 π1 : ℝ) (p0 p1 : B → ℝ)
    (δ : B → Fin 2) : ℝ :=
  π0 * ∑ b, ((δ b : ℕ) : ℝ) * p0 b + π1 * ∑ b, (1 - ((δ b : ℕ) : ℝ)) * p1 b

end FuchsThesis.Chernoff


