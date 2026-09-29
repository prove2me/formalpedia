-- Prove2me | Definitions.Def_Roberts1997_RWM_IsRegularTarget
-- name    : Roberts1997_RWM_IsRegularTarget
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:43:13.73969+00:00
-- url     : https://prove2.me/theorems/f0284608-e950-46f5-9cb1-7da81ca87601
-- title:
--   Standing hypotheses on the target density f: positive, C², a probability density, f′/f Lipschitz, (A1), (A2)
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be the one-dimensional target density of Roberts, Gelman and Gilks (1997). The paper's standing hypotheses on $f$ (pp. 111–112) are collected in one predicate. $f$ is **regular** when
--
--   1. $f(x)>0$ for every $x\in\mathbb R$;
--   2. $f$ is $C^2$;
--   3. $f$ is a probability density: $\int_{\mathbb R} f(x)\,dx = 1$;
--   4. $f'/f$ is Lipschitz continuous;
--   5. (A1) $\mathbb E_f\big[(f'(X)/f(X))^8\big] <\infty$;
--   6. (A2) $\mathbb E_f\big[(f''(X)/f(X))^4\big] <\infty$.
--
--   Here $\mathbb E_f[g(X)] = \int g(x) f(x)\,dx$. Conditions (A1) and (A2) read
--
--   $$
--   \int_{\mathbb R}\Big(\frac{f'(x)}{f(x)}\Big)^8 f(x)\,dx<\infty,\qquad \int_{\mathbb R}\Big(\frac{f''(x)}{f(x)}\Big)^4 f(x)\,dx<\infty .
--   $$
--
--   Every result of the mission assumes these hypotheses.
--
--   **Formalization Note** The paper calls $\pi_n$ a "product density" and draws the initial components "according to $f$", so $f$ is read as a probability density (item 3). "f′/f is Lipschitz continuous" is stated once before (A1) and not repeated in Theorem 1.1; it is a standing assumption and is carried here. Finiteness of the expectations is encoded as Lebesgue integrability of the integrands, never as "the Bochner integral is finite" (which would hold trivially for a non-integrable integrand). The constant $M$ in (A1) only names the value and is not needed.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, pp. 111–112, standing assumptions: f positive and C² (Theorem 1.1), f′/f Lipschitz, (A1), (A2)

import Mathlib

open MeasureTheory

namespace Roberts1997.RWM

/-- Standing hypotheses of Roberts–Gelman–Gilks (1997), pp. 111–112, on the one-dimensional
target density `f`: `f` is positive, `C²`, a probability density on `ℝ`, `f'/f` is Lipschitz,
and the moment conditions (A1) `𝔼_f[(f'/f)^8] < ∞` and (A2) `𝔼_f[(f''/f)^4] < ∞` hold.
Expectations under `f` are Lebesgue integrals against the density `f`; finiteness is stated as
integrability (never as a Bochner integral being finite). -/
structure IsRegularTarget (f : ℝ → ℝ) : Prop where
  /-- `f` is positive. -/
  pos : ∀ x, 0 < f x
  /-- `f` is `C²`. -/
  contDiff : ContDiff ℝ 2 f
  /-- `f` is a probability density with respect to Lebesgue measure. -/
  integral_eq_one : ∫ x, f x = 1
  /-- `f'/f` is Lipschitz continuous. -/
  lipschitz_logDeriv : ∃ K : NNReal, LipschitzWith K (fun x => deriv f x / f x)
  /-- (A1): `𝔼_f[(f'(X)/f(X))^8] < ∞`. -/
  A1 : Integrable (fun x => (deriv f x / f x) ^ 8 * f x)
  /-- (A2): `𝔼_f[(f''(X)/f(X))^4] < ∞`. -/
  A2 : Integrable (fun x => (deriv (deriv f) x / f x) ^ 4 * f x)

end Roberts1997.RWM


