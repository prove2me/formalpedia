-- Prove2me | Definitions.Def_FuchsThesis_Chernoff_bayesError
-- name    : FuchsThesis_Chernoff_bayesError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:16.338496+00:00
-- url     : https://prove2.me/theorems/c0b44ca6-1111-4572-8e12-e86fbfa8817e
-- title:
--   Bayes error probability $P_e = \sum_b \min\{\pi_0 p_0(b), \pi_1 p_1(b)\}$, eq. (2.11)
-- statement:
--   For priors $\pi_0, \pi_1$ and distributions $p_0, p_1$ on a finite outcome set $\{1,\dots,n\}$, the **probability of error of Bayes' decision method** is
--
--   $$
--   P_e = \sum_{b=1}^{n} \min\{\pi_0 p_0(b),\, \pi_1 p_1(b)\}.
--   $$
--
--   The smaller it is, the more distinguishable the two distributions are relative to the prior $\{\pi_0, \pi_1\}$. That it equals $P_e(\delta_B)$ for every Bayes decision function $\delta_B$ is equation (2.11), formalized as a milestone of this mission.
--
--   **Formalization Note** The outcome set is an arbitrary finite type; the definition accepts any real priors and functions.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.2.1, eq. (2.11), p.15 (PDF p.24)

import Mathlib

namespace FuchsThesis.Chernoff

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §2.2.1, eq. (2.11), p.15 (PDF p.24).

The probability of error of Bayes' decision method,
`Pe = ∑_{b=1}^{n} min{π0 p0(b), π1 p1(b)}`.

**Formalization Note.** The outcome set is an arbitrary finite type `B`. Defined for any real
priors and functions; that this is the error probability of every Bayes decision function is the
theorem `FuchsThesis.Chernoff.eq_2_11`. -/
noncomputable def bayesError {B : Type} [Fintype B] (π0 π1 : ℝ) (p0 p1 : B → ℝ) : ℝ :=
  ∑ b, min (π0 * p0 b) (π1 * p1 b)

end FuchsThesis.Chernoff


