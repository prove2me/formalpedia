-- Prove2me | Definitions.Def_FuchsVdGraaf_errorProb
-- name    : FuchsVdGraaf_errorProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:15.111446+00:00
-- url     : https://prove2.me/theorems/a8f13669-a57f-4d2b-89d9-0c12ed5f94fa
-- title:
--   Probability of error $\mathrm{PE}(p_0,p_1)$ (Definition 3)
-- statement:
--   For two probability distributions $p_0, p_1$ on a finite set $\mathcal X$, the **probability of error** is
--
--   $$
--   \mathrm{PE}(p_0,p_1) = \frac12 \sum_{x\in\mathcal X} \min\{p_0(x), p_1(x)\} .
--   $$
--
--   It is the probability that an observer who receives one sample, drawn with probability $\tfrac12$ from $p_0$ and $\tfrac12$ from $p_1$, guesses the source wrongly when using the optimal (Bayes) strategy. Identical distributions have $\mathrm{PE} = \tfrac12$, orthogonal ones $\mathrm{PE} = 0$.
--
--   **Formalization Note** Defined for any real functions on a finite type; the theorems assume both arguments are probability distributions.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Definition 3, eq. (11), p.10

import Mathlib

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Definition 3, eq. (11), p.10: the
(classical) probability of error between two probability distributions with equal priors,
`PE(p₀, p₁) = ½ ∑_{x∈X} min{p₀(x), p₁(x)}`.

**Formalization Note.** Defined for any real functions on a finite type; theorems assume both
are probability distributions (`IsProbDist`). -/
noncomputable def errorProb {X : Type} [Fintype X] (p0 p1 : X → ℝ) : ℝ :=
  (1 / 2) * ∑ x, min (p0 x) (p1 x)

end FuchsVdGraaf


