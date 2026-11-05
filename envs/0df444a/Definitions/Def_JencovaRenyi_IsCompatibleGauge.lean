-- Prove2me | Definitions.Def_JencovaRenyi_IsCompatibleGauge
-- name    : JencovaRenyi_IsCompatibleGauge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:27.035419+00:00
-- url     : https://prove2.me/theorems/747762c8-31d4-4111-95e1-ae38c81b897b
-- title:
--   A normed subspace $X_0$ continuously embedded in $X_1$ (a compatible pair)
-- statement:
--   A gauge $n_0 : X_1\to[0,\infty]$ on a normed complex space $X_1$ describes a **compatible pair** $(X_0, X_1)$ with $X_0 = \{n_0<\infty\}$ continuously embedded in $X_1$ when
--
--   1. $n_0(0) = 0$, $n_0(x+y)\le n_0(x)+n_0(y)$ and $n_0(cx) = |c|\,n_0(x)$ for $c\ne0$ (so $X_0$ is a subspace and $n_0$ a seminorm on it);
--   2. $n_0(x) = 0$ implies $x = 0$ (a norm);
--   3. there is $C\ge0$ with $\|x\|_{X_1}\le C\,n_0(x)$ for all $x\in X_0$.
--
--   It is the setting of the abstract Riesz–Thorin theorem (Theorem B.1).
--
--   **Formalization Note** Completeness of $X_0$ and $X_1$ is not required.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, Appendix B, p.22 ("it is enough to assume that $X_0$ is continuously embedded in $X_1$")

import Mathlib

open scoped ENNReal

namespace JencovaRenyi

/-- A compatible pair `(X₀, X₁)` with `X₀` continuously embedded in `X₁` (Jenčová,
arXiv:1609.08462v4, Appendix B, p.22: "it is enough to assume that `X₀` is continuously embedded
in `X₁`"), encoded by the gauge `n₀ : X₁ → [0, ∞]` of `X₀`: `X₀ = {n₀ < ∞}` is a linear subspace
on which `n₀` is a norm, and `‖x‖₁ ≤ C ‖x‖₀` on `X₀`.

**Formalization Note.** Completeness of `X₀` and `X₁` is not part of this predicate. -/
structure IsCompatibleGauge {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (n₀ : X → ℝ≥0∞) : Prop where
  zero : n₀ 0 = 0
  add_le : ∀ x y, n₀ (x + y) ≤ n₀ x + n₀ y
  smul : ∀ (c : ℂ) x, c ≠ 0 → n₀ (c • x) = (‖c‖₊ : ℝ≥0∞) * n₀ x
  eq_zero : ∀ x, n₀ x = 0 → x = 0
  embedding : ∃ C : NNReal, ∀ x, n₀ x < ⊤ → (‖x‖₊ : ℝ≥0∞) ≤ C * n₀ x

end JencovaRenyi


