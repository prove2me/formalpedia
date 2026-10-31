-- Prove2me | Definitions.Def_TestScoreSubmod_HasExtendedDiminishingReturns
-- name    : TestScoreSubmod_HasExtendedDiminishingReturns
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:09.655983+00:00
-- url     : https://prove2.me/theorems/262c113f-d948-4c11-9ad6-93ff91833e4e
-- title:
--   Extended diminishing returns, Definition 1
-- statement:
--   Let $g:\mathbb R_+^{n}\to\mathbb R$ with $n=m+1$. For $z\in\mathbb R_+^{n-1}$ and $x\in\mathbb R_+$ write $g(z,x)$ for the value of $g$ at $z$ extended by one coordinate $x$, and $g(z)=g(z,0)$. The function $g$ has the **extended diminishing returns** property if for every value $v=g(z_0)$ with $z_0\in\mathbb R_+^{n-1}$ there is $z\in\mathbb R_+^{n-1}$ such that
--
--   1. $g(z)=v$, and
--   2. for all $y\in\mathbb R_+^{n-1}$ with $g(y)\le v$ and all $x\in\mathbb R_+$,
--   $$
--   g(z,x)-g(z)\le g(y,x)-g(y).
--   $$
--
--   Adding an item of performance $x$ to a group worth $v$ (represented by $z$) gains no more than adding it to any group worth at most $v$.
--
--   **Formalization Note** $g(z,x)$ is `g (Fin.snoc z x)`; for a symmetric $g$ the position of the new coordinate is irrelevant. Printed Definition 1 asks for such a $z$ for every $v\ge0$ with a preimage in $\mathbb R_+^n$; here $v$ ranges over the values attained on $\mathbb R_+^{n-1}$ (padded with $0$), a subset of those values, so the printed property implies this one (form (13) of Appendix A at $d=n-1$). Symmetry and submodularity are separate hypotheses.
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, Definition 1, p.16; Appendix A, (13), p.33

import Mathlib

open scoped NNReal

namespace TestScoreSubmod

/-- **Extended diminishing returns** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, Definition 1,
p.16; the form (13) of Appendix A, p.33, at dimension `d = n − 1`).

Write `n = m + 1` and `g(z, x)` for `g` at the vector `z ∈ ℝ₊^{n−1}` extended by one more
coordinate `x`, and `g(z) = g(z, 0)`. `g` has the extended diminishing returns property if for
every value `v = g(z₀)` attained on `ℝ₊^{n−1}` there is `z ∈ ℝ₊^{n−1}` with

* (a) `g(z) = v`, and
* (b) for all `y ∈ ℝ₊^{n−1}` with `g(y) ≤ v`: `g(z, x) − g(z) ≤ g(y, x) − g(y)` for all `x ∈ ℝ₊`.

**Formalization Note** `g(z, x)` is `g (Fin.snoc z x)` (the new coordinate is the last one;
for a symmetric `g` its position is irrelevant) and `g(z)` is `g (Fin.snoc z 0)`, with
`φ = 0`. Printed Definition 1 quantifies over every `v` with a preimage in `ℝ₊ⁿ`; here `v` ranges
over the values attained on `ℝ₊^{n−1}` (padded with `0`), which is a subset of those values, so
the printed property implies this one. Symmetry and submodularity, which Definition 1 presupposes,
are separate hypotheses wherever this property is used. -/
def HasExtendedDiminishingReturns {m : ℕ} (g : (Fin (m + 1) → ℝ≥0) → ℝ) : Prop :=
  ∀ z₀ : Fin m → ℝ≥0, ∃ z : Fin m → ℝ≥0,
    g (Fin.snoc (α := fun _ => ℝ≥0) z 0) = g (Fin.snoc (α := fun _ => ℝ≥0) z₀ 0) ∧
    ∀ y : Fin m → ℝ≥0,
      g (Fin.snoc (α := fun _ => ℝ≥0) y 0) ≤ g (Fin.snoc (α := fun _ => ℝ≥0) z 0) →
      ∀ x : ℝ≥0,
        g (Fin.snoc (α := fun _ => ℝ≥0) z x) - g (Fin.snoc (α := fun _ => ℝ≥0) z 0) ≤
          g (Fin.snoc (α := fun _ => ℝ≥0) y x) - g (Fin.snoc (α := fun _ => ℝ≥0) y 0)

end TestScoreSubmod


