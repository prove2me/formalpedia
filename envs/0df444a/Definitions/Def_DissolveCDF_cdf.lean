-- Prove2me | Definitions.Def_DissolveCDF_cdf
-- name    : DissolveCDF_cdf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:09.986966+00:00
-- url     : https://prove2.me/theorems/152aa778-dd52-40e1-aedf-cd6462d8a00b
-- title:
--   (CDF) — the constraint dissolving function $h$
-- statement:
--   Given $f:\mathbb R^n\to\mathbb R$, $c:\mathbb R^n\to\mathbb R^p$, a constraint dissolving operator $\mathcal A:\mathbb R^n\to\mathbb R^n$ and a penalty parameter $\beta\in\mathbb R$, the **constraint dissolving function** is
--
--   $$
--   h(x):=f(\mathcal A(x))+\frac\beta2\|c(x)\|^2. \tag{CDF}
--   $$
--
--   Minimizing $h$ over all of $\mathbb R^n$ replaces the constrained problem (OCP); since $\mathcal A(x)=x$ on $\mathcal M$, $h=f$ on the feasible set.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §1.3, (CDF), p.4

import Mathlib

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, (CDF) (p.4): the **constraint dissolving function**
`h(x) := f(A(x)) + (β/2) ‖c(x)‖²` with penalty parameter `β`.

**Formalization Note** `β` is any real number; the paper's results assume `β ≥ β_x`. -/
noncomputable def cdf {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f (A x) + β / 2 * ‖c x‖ ^ 2

end DissolveCDF


