-- Prove2me | Definitions.Def_ABPOnline_heatSG
-- name    : ABPOnline_heatSG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:40.281203+00:00
-- url     : https://prove2.me/theorems/1ebc14b3-14cb-4646-92d6-c5531ff7c3f5
-- title:
--   Heat semigroup $P_s$ and Föllmer feedback $v(t,x)=\partial_x\log P_{h-t}f(x)$
-- statement:
--   Let $\gamma_s=N(0,s)$. The one-dimensional **heat semigroup** acts on $f:\mathbb R\to\mathbb R$ by
--   $$
--   P_sf(x)=\int f(x+y)\,\gamma_s(dy),
--   $$
--   and the **Föllmer feedback** of $f$ on the horizon $h$ is
--   $$
--   v(t,x):=\partial_x\log P_{h-t}f(x),\qquad 0\le t<h .
--   $$
--
--   The final-block feedback $v_N$ of Algorithm 1 is of this form, for a compactly supported log-concave terminal density.
--
--   **Formalization Note** The integral is a Bochner integral ($0$ for a non-integrable integrand; for the log-concave $f$ of Lemma C.3 the integrand is integrable). The derivative is Lean's `deriv` ($0$ where the function is not differentiable), so statements using $v$ assert differentiability separately.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), §C.1, p.36 (PDF p.37); Lemma C.3, p.40 (PDF p.41)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ABPOnline

/-- The one-dimensional heat semigroup `P_s f(x) = ∫ f(x + y) dγ_s(y)`, `γ_s = N(0, s)`
(arXiv:2609.02124, §C.1, printed p.36, PDF p.37).

**Formalization Note** A Bochner integral: it is `0` when `f(x + ·)` is not `γ_s`-integrable. For
the log-concave `f` of Lemma C.3 it is integrable (a log-concave function is bounded by the
exponential of an affine function). The variance is `s.toNNReal`, which matters only for `s > 0`. -/
noncomputable def heatSG (s : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, f (x + y) ∂(gaussianReal 0 s.toNNReal)

/-- The Föllmer feedback `v(t, x) = ∂ₓ log P_{h−t} f(x)`, `0 ≤ t < h` (arXiv:2609.02124, Lemma C.1,
p.36, and Lemma C.3, printed p.40, PDF p.41). -/
noncomputable def follmerV (h : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun y => Real.log (heatSG (h - t) f y)) x

end ABPOnline


