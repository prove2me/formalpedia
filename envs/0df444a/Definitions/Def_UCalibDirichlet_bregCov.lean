-- Prove2me | Definitions.Def_UCalibDirichlet_bregCov
-- name    : UCalibDirichlet_bregCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:09.941503+00:00
-- url     : https://prove2.me/theorems/2f36c211-54cd-4d41-a004-92739850b8f9
-- title:
--   Covariance $\mathrm{Cov}_{X\sim\mathrm{Beta}(b,m)}(f'(X),X)$ in symmetric form
-- statement:
--   For a convex $f$ on $[0,1]$ and $b,m>0$, with $X,Y$ independent $\mathrm{Beta}(b,m)$ variables,
--   $$\mathrm{Cov}(f'(X),X)=\tfrac12\,\mathbb E\big[(f'(X)-f'(Y))(X-Y)\big]\in[0,+\infty].$$
--   This is the symmetric form (12) of the covariance used in the curvature $W^i_F$ (11) and in Lemma 1.7. Since $f'$ is non-decreasing the integrand is nonnegative, so the expectation is always defined, possibly $+\infty$.
--
--   **Formalization Note** $f'$ is the derivative of $f$ (it exists except at countably many points, which a Beta law does not charge). The value lies in $[0,+\infty]$ and equals the usual covariance whenever $f'(X)$ is integrable; using this form avoids the default value $0$ of the integral of a non-integrable function. The positive part in the integrand only matters for non-convex $f$, which is never used.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), displays (11)–(12), p.5; Lemma 1.7, p.5

import Mathlib

open MeasureTheory

namespace UCalibDirichlet

/-- **The covariance `Cov_{X∼Beta(b,m)}(f′(X), X)`, in the symmetric form of display (12).**
Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027 submission), p.5: (11) uses
`Cov_{X∼Beta(a_i,‖a_{−i}‖₁)}(f′_{i,R}(X), X)`, and (12) gives the equivalent form "(simply based on
the definition of covariance)" `½ E_{X,Y}[(f′(X) − f′(Y))(X − Y)]` with "`X` and `Y` two independent
samples of `Beta(a_i, ‖a_{−i}‖₁)`"; Lemma 1.7 (p.5) uses `Cov(f′(X), X)` for `X ∼ Beta(a, m)`.

`bregCov f b m = ∫⁻ ½ (f′(x) − f′(y))(x − y)⁺ d(Beta(b,m) ⊗ Beta(b,m))(x, y)`, in `[0, +∞]`.

**Formalization Note.** For convex `f`, `f′` is non-decreasing, so the integrand is nonnegative
(almost surely: `f′` is `deriv f`, whose junk value `0` at the countably many kinks of `f` is
invisible to the atomless Beta law, as in the paper's footnote 2). Then `bregCov f b m` equals
`Cov(f′(X), X)` whenever `f′(X)` is integrable, and is `+∞` when the covariance diverges. Using
the nonnegative form avoids the junk value `0` of a Bochner integral of a non-integrable
function (for non-integer parameters `f′(X)` need not be integrable). The positive-part
truncation only matters for non-convex `f`, which never occurs. -/
noncomputable def bregCov (f : ℝ → ℝ) (b m : ℝ) : ENNReal :=
  ∫⁻ z : ℝ × ℝ, ENNReal.ofReal ((deriv f z.1 - deriv f z.2) * (z.1 - z.2) / 2)
    ∂((ProbabilityTheory.betaMeasure b m).prod (ProbabilityTheory.betaMeasure b m))

end UCalibDirichlet


