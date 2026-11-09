-- Prove2me | Definitions.Def_PhiSobBayes_testClass
-- name    : PhiSobBayes_testClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:04:59.108777+00:00
-- url     : https://prove2.me/theorems/609f3dbb-76d7-4336-8e28-71a7f362ec45
-- title:
--   Test class $\mathcal A^J_0$: constants plus $C_c^\infty$ functions with values in $J$
-- statement:
--   For $n\ge 0$ and an open interval $J\subseteq\mathbb R$, the **test class** is
--   $$\mathcal A^J_0=\{f=c+g:\ c\in\mathbb R,\ g\in C^\infty_c(\mathbb R^n),\ f(\mathbb R^n)\subseteq J\},$$
--   the smooth functions with values in $J$ that are constant outside a compact set. Here $g$ is smooth (continuous partial derivatives of all orders) and has compact support (the closure of $\{g\neq 0\}$ is bounded).
--
--   Every functional inequality of the mission is tested on this class. A test function is bounded with bounded gradient, so all expectations in the inequalities are finite for every probability measure.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; smooth is `ContDiff ℝ ∞`, compact support is `HasCompactSupport`.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 2.1, p.14 (PDF 14); Definition 8, p.54 (PDF 54)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- The **test class** `A^J_0` on `ℝⁿ`: functions `f = c + g` with `c ∈ ℝ` and `g` smooth with
compact support, taking all their values in `J`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 2.1, p.14 (PDF 14): "A^J_0 = {𝑓 = 𝑐 + 𝑔 : 𝑐 ∈ ℝ, 𝑔 ∈ 𝐶^∞_𝑐(ℝ𝑛), 𝑓(ℝ𝑛) ⊆ 𝐽} of smooth
functions with values in 𝐽 that are constant outside a compact set"; Definition 8, p.54 (PDF 54):
smooth means continuous partial derivatives of all orders, compact support means the closure of
`{g ≠ 0}` is bounded.

**Formalization Note** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)` (Euclidean norm). Smooth is
`ContDiff ℝ ∞` (`C^∞`, not analytic), compact support is `HasCompactSupport`. -/
def testClass (n : ℕ) (J : Set ℝ) : Set (EuclideanSpace ℝ (Fin n) → ℝ) :=
  {f | (∃ (c : ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      f = fun x => c + g x) ∧ ∀ x, f x ∈ J}

end PhiSobBayes


