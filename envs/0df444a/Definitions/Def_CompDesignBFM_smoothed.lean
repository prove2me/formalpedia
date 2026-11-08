-- Prove2me | Definitions.Def_CompDesignBFM_smoothed
-- name    : CompDesignBFM_smoothed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:35.708854+00:00
-- url     : https://prove2.me/theorems/4f72ca00-8145-44fb-8bba-7395aabfd5a8
-- title:
--   Smoothed value function
-- statement:
--   Let $R_q(S)$ retain each element of $S$ independently with probability $q$. The **smoothed value** is
--
--   $$\tilde v(S)=\int_0^1\mathbb E[v(R_q(S))]\,dq=\sum_{T\subseteq S}v(T)\int_0^1 q^{|T|}(1-q)^{|S|-|T|}\,dq.$$
--
--   For a subadditive $v$ it is a self-bounding proxy within a factor 2.
--
--   **Formalization Note** The expectation is written out as the finite sum (Remark 3.1, first equality). The integrand is a polynomial in $q$, hence integrable (`smoothed_integrand_intervalIntegrable`), and the exponent $|S|-|T|$ is exact since $T\subseteq S$.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 3.1, eq. (9), p.19 (PDF 21)

import Mathlib

namespace CompDesignBFM

/-- The smoothed value `ṽ(S) = ∫₀¹ E[v(R_q(S))] dq` (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 3.1, eq. (9), p.19, PDF 21).
**Formalization Note.** `E[v(R_q(S))]` is written out as `∑_(T ⊆ S) q^|T| (1 - q)^(|S|-|T|) v(T)`, the
first equality of Remark 3.1, p.19, and of Lemma D.1's proof, p.50. The natural-number subtraction is
exact since `T ⊆ S`. The integrand is a polynomial in `q`, hence integrable
(`smoothed_integrand_intervalIntegrable`). -/
noncomputable def smoothed {n : ℕ} (v : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∫ q in (0 : ℝ)..1, ∑ T ∈ S.powerset, q ^ T.card * (1 - q) ^ (S.card - T.card) * v T

/-- The integrand of `smoothed` is integrable on `[0, 1]`, so the integral has no junk value. -/
theorem smoothed_integrand_intervalIntegrable {n : ℕ} (v : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    IntervalIntegrable (fun q : ℝ => ∑ T ∈ S.powerset, q ^ T.card * (1 - q) ^ (S.card - T.card) * v T)
      MeasureTheory.volume 0 1 :=
  Continuous.intervalIntegrable (by fun_prop) _ _

end CompDesignBFM


