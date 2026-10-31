-- Prove2me | Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveFun
-- name    : KallMayerSLP_GenConcave_IsGammaConcaveFun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:42.531123+00:00
-- url     : https://prove2.me/theorems/ca43ad75-8be0-4457-86fc-805f9b732530
-- title:
--   $\gamma$-concave functions (Definition 2.3)
-- statement:
--   A nonnegative function $f:\mathbb R^n\to\mathbb R_+$ is **$\gamma$-concave**, for $\gamma\in[-\infty,\infty]$, if for any $x,y\in\mathbb R^n$ and $\lambda\in[0,1]$
--
--   $$
--   f(\lambda x+(1-\lambda)y)\ \ge\ \mathcal M_\gamma^\lambda\bigl(f(x),f(y)\bigr).
--   $$
--
--   For $\gamma=0$ this is log-concavity, for $\gamma=1$ concavity on the positivity set $\{f>0\}$, for $\gamma=-\infty$ quasi-concavity; for $0<\gamma<\infty$ it says $f^\gamma$ is concave on $\{f>0\}$, for $-\infty<\gamma<0$ that $f^\gamma$ is convex there, and for $\gamma=+\infty$ that $f$ is constant there.
--
--   **Formalization Note** The domain is any real vector space $E$; the book's case is $E=\mathbb R^n$ (`Fin n → ℝ`), and the product $\mathbb R^n\times\mathbb R^m$ is used for $\mathbb R^{n+m}$ in Theorem 2.9. Nonnegativity of $f$ is part of the predicate. The inequality is required at every pair of points.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Definition 2.3, p.123 (PDF 133)

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_genMean

namespace KallMayerSLP.GenConcave

/-- A **`γ`-concave function** (Kall & Mayer, *Stochastic Linear Programming* (2005),
Chapter 2, Definition 2.3, p. 123, PDF p. 133): a nonnegative function `f` such that for
all `x, y` and `λ ∈ [0, 1]`
`f(λx + (1 − λ)y) ≥ M_γ^λ(f(x), f(y))`.

`γ = 0` is log-concavity (Definition 1.3, p. 90), `γ = 1` concavity on `{f > 0}`, `γ = −∞`
quasi-concavity (p. 123).

**Formalization Note.** The book states the definition for `f : ℝⁿ → ℝ₊`; here the domain
is any real vector space `E` (`E = Fin n → ℝ` is the book's case), so that the same
predicate applies to functions on `ℝⁿ × ℝᵐ ≅ ℝⁿ⁺ᵐ` (Theorem 2.9). Nonnegativity is part of
the predicate; `γ ∈ EReal`. The inequality is required at every pair of points, not
almost everywhere. -/
def IsGammaConcaveFun {E : Type*} [AddCommGroup E] [Module ℝ E]
    (γ : EReal) (f : E → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
    ∀ x y : E, ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      genMean γ lam (f x) (f y) ≤ f (lam • x + (1 - lam) • y)

end KallMayerSLP.GenConcave


