-- Prove2me | Definitions.Def_ExactModKL_hfun
-- name    : ExactModKL_hfun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:56:01.056104+00:00
-- url     : https://prove2.me/theorems/dd38799e-4a46-48cc-83d6-57cef8068b96
-- title:
--   The function $h(s)$ of Definition 3.6
-- statement:
--   Let $f:\mathbb R^n\to(-\infty,\infty]$, $\bar x\in\mathbb R^n$, $U\subseteq\mathbb R^n$ and $\eta\in(0,\infty]$. For $s\in(0,\eta)$,
--   $$
--   h(s)=\sup\Big\{\operatorname{dist}^{-1}\big(0,\partial f(x)\big):\ x\in U\cap[0<f-f(\bar x)<\eta],\ s\le f(x)-f(\bar x)\Big\}\in[0,\infty].
--   $$
--   The integral of $h$ is the exact modulus. Using the level set $s\le f(x)-f(\bar x)$ rather than $s=f(x)-f(\bar x)$ makes $h$ nonincreasing in $s$.
--
--   **Formalization Note** $h$, $\operatorname{dist}$ and $\operatorname{dist}^{-1}$ take values in $[0,\infty]$, with $\infty^{-1}=0$, $0^{-1}=\infty$ and $\sup\emptyset=0$. The paper's assumption "$h(s)<\infty$" is not built into the definition; it is a conclusion of Proposition 3.9. The paper takes $U\subseteq\operatorname{dom}\partial f$; here $U$ is any set, and a point with $\partial f(x)=\emptyset$ contributes $0$.
-- source:
--   Wang–Wang, arXiv:2008.13257v5, Definition 3.6, p.11

import Mathlib
import Definitions.Def_ExactModKL_dist0

open scoped ENNReal

namespace ExactModKL

/-- The function `h` of Definition 3.6 (Wang–Wang, arXiv:2008.13257v5 (preprint), p.11):
`h(s) = sup{dist⁻¹(0, ∂f(x)) : x ∈ U ∩ [0 < f − f(x̄) < η], s ≤ f(x) − f(x̄)}`.

**Formalization Note.** `h` is `ℝ≥0∞`-valued: `dist⁻¹` is the inverse in `ℝ≥0∞`
(`∞⁻¹ = 0`, `0⁻¹ = ∞`) and the supremum is taken in `ℝ≥0∞`, so `sup ∅ = 0` and an unbounded
set gives `∞` (Definition 3.6's hypothesis "h(s) < ∞" is then a statement, proved in
Proposition 3.9, not an assumption of the definition). The band and the level condition are
computed in `EReal`. The paper takes `U ⊆ dom ∂f`; here `U` is any set, and a point of `U` with
`∂f(x) = ∅` contributes `∞⁻¹ = 0`, i.e. nothing. Only `s ∈ (0, η)` is used. -/
noncomputable def hfun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar : EuclideanSpace ℝ (Fin n)) (U : Set (EuclideanSpace ℝ (Fin n))) (η : ℝ≥0∞)
    (s : ℝ) : ℝ≥0∞ :=
  ⨆ (x : EuclideanSpace ℝ (Fin n))
    (_ : x ∈ U ∧ 0 < f x - f xbar ∧ f x - f xbar < (η : EReal) ∧ (s : EReal) ≤ f x - f xbar),
    (dist0 f x)⁻¹

end ExactModKL


