-- Prove2me | Definitions.Def_FuchsThesis_Chernoff_errorProbN
-- name    : FuchsThesis_Chernoff_errorProbN
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:06.131393+00:00
-- url     : https://prove2.me/theorems/2b7b26be-6864-4e2c-a962-69e6555fcea1
-- title:
--   Bayes error $P_e(N)$ after $N$ samplings
-- statement:
--   Let $P_e(N)$ be the probability of error for Bayes' decision rule after sampling $N$ times one of the two distributions $p_0, p_1$ (priors $\pi_0, \pi_1$). It is the Bayes error (2.11) of the decision problem whose outcomes are the strings $b_1\dots b_N$, distributed by the product distributions:
--
--   $$
--   P_e(N) = \sum_{b_1 b_2 \dots b_N} \min\bigl\{\pi_0\, p_0(b_1 \dots b_N),\ \pi_1\, p_1(b_1 \dots b_N)\bigr\}.
--   $$
--
--   The Chernoff bound describes how fast $P_e(N)$ decreases to zero as $N$ grows.
--
--   **Formalization Note** Strings are functions from $\mathrm{Fin}\,N$ to the outcome type. The first line of (2.28) prints the second argument of the minimum as $\pi_0 p_0(b_1\dots b_N)$; $\pi_1 p_1(b_1\dots b_N)$ is meant.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Theorem 2.1 and eq. (2.28), pp.16–17 (PDF pp.25–26)

import Mathlib
import Definitions.Def_FuchsThesis_Chernoff_bayesError
import Definitions.Def_FuchsThesis_Chernoff_productDist

namespace FuchsThesis.Chernoff

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Theorem 2.1 and eq. (2.28) (first line), pp.16–17 (PDF pp.25–26).

`Pe(N)`, the probability of error for Bayes' decision rule after sampling `N` times one of the
two distributions: Bayes' error (2.11) of the decision problem whose outcomes are the strings
`b⃗ ∈ B^N`, with the product distributions (2.21)–(2.22),
`Pe(N) = ∑_{b1 b2 … bN} min{π0 p0(b1 … bN), π1 p1(b1 … bN)}`.

**Formalization Note.** Strings are functions `Fin N → B`. The first line of (2.28) prints the
second argument of the min as `π0 p0(b1 … bN)`; `π1 p1(b1 … bN)` is meant (it is (2.11) for the
`N`-sample problem, and the next line of (2.28) uses `π1`). -/
noncomputable def errorProbN {B : Type} [Fintype B] (π0 π1 : ℝ) (p0 p1 : B → ℝ) (N : ℕ) : ℝ :=
  bayesError π0 π1 (productDist p0 N) (productDist p1 N)

end FuchsThesis.Chernoff


