-- Prove2me | Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_VariationalBounds
-- name    : LinearHashingPoissonesque_ExpectedLoads_VariationalBounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T19:01:16.113828+00:00
-- url     : https://prove2.me/theorems/c29eec7d-841e-45cb-bb92-771f5bb2332a
-- title:
--   Signed variational bounds for extreme-bin expectations
-- statement:
--   For real $\mu\ge0$, integers $1\le r\le n$ and $\lambda\ne0$, put
--
--   $$V(\mu,n,r;\lambda)=\frac{\mu(e^\lambda-1)+\log(n/r)}{\lambda},\quad V^- =\sup_{\lambda<0}V(\mu,n,r;\lambda),\quad V^+=\inf_{\lambda>0}V(\mu,n,r;\lambda).$$
--
--   The two strict sign domains exclude division by zero. Each is nonempty. The negative-parameter image is bounded above by $\mu$, and the positive-parameter image is bounded below by $\mu$, so the real extrema are meaningful without assuming an attained optimizer. These analytic facts are proved in the local verification module. Corollary 1 compares both extreme-bin expectations to these quantities.
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.13, Corollary 1 and its displayed variational expressions; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Mathlib

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Corollary 1, p.13: the real variational expression, used only at λ ≠ 0. -/
noncomputable def variationalValue (mu : ℝ) (n r : ℕ) (lam : ℝ) : ℝ :=
  (mu * (Real.exp lam - 1) + Real.log ((n : ℝ) / (r : ℝ))) / lam

/-- Strictly negative parameters; the source supremum need not be attained. -/
noncomputable def variationalLower (mu : ℝ) (n r : ℕ) : ℝ :=
  sSup {z : ℝ | ∃ lam : ℝ, lam < 0 ∧ z = variationalValue mu n r lam}

/-- Strictly positive parameters; the source infimum need not be attained. -/
noncomputable def variationalUpper (mu : ℝ) (n r : ℕ) : ℝ :=
  sInf {z : ℝ | ∃ lam : ℝ, 0 < lam ∧ z = variationalValue mu n r lam}

end LinearHashingPoissonesque.ExpectedLoads


