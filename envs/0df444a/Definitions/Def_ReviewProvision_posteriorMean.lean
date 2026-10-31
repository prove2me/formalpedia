-- Prove2me | Definitions.Def_ReviewProvision_posteriorMean
-- name    : ReviewProvision_posteriorMean
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:54:21.474783+00:00
-- url     : https://prove2.me/theorems/a98c4cc3-cdf1-42b2-a5c6-c22b5dca5162
-- title:
--   The customer evaluation $v_{\psi n}=\mathbb E[q+t_n\mid\cdot]$
-- statement:
--   Under a policy $\psi$ and sales $\vec k$, the **customer evaluation** in cluster $n$ is the posterior mean of the cluster value given the customer's information:
--
--   $$
--   v_{\psi n}(\vec k)=\mathbb E\bigl[q+t_n\mid \text{information of }\psi,n\bigr].
--   $$
--
--   **Formalization Note** This is a Mathlib conditional expectation of the model. The closed forms (1), (2), (11) and the JP display of p.24 are theorems of the mission, not the definition.
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), (1), p.11; (2), p.12; p.13; (11), p.23; p.24

import Mathlib
import Definitions.Def_ReviewProvision_info

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **The customer evaluation** `v_{ψn} = E[q + t_n | information of ψ, n]`: the posterior mean of the
cluster value. SSRN 3403322 (manuscript of 2021-05-24), (1), p.11, (2), p.12, p.13 ("let
`v_{ψn} = E[q + t_n]` be the posterior expected cluster value"), (11), p.23, and the first display of
p.24.

**Formalization Note.** A Mathlib conditional expectation of the model, never the closed forms
(1), (2), (11), which are theorems here (`eq_1`, `eq_2`, `eq_11`, `jp_posterior_mean`). `info_le` shows
that the σ-algebra is below the ambient one, and `q + t_n` is integrable, so this is the genuine
conditional expectation. It is defined up to a null set, and every use of it (the integral in
`profit`, `Var`, laws) does not depend on the version. -/
noncomputable def posteriorMean {N : ℕ} (p : Params) (k : Fin N → ℝ) (ψ : Policy) (n : Fin N) :
    Sample N → ℝ :=
  (prior p N)[fun ω => quality ω + taste ω n | info p k ψ n]

end ReviewProvision


