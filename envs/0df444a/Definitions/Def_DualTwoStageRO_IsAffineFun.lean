-- Prove2me | Definitions.Def_DualTwoStageRO_IsAffineFun
-- name    : DualTwoStageRO_IsAffineFun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:10.390257+00:00
-- url     : https://prove2.me/theorems/76c31502-6f61-40ff-8507-efb7ec3146f2
-- title:
--   Affine function $\mathbb R^n\to\mathbb R$
-- statement:
--   A function $h:\mathbb R^n\to\mathbb R$ is **affine** if there are $a\in\mathbb R^n$ and $c\in\mathbb R$ with
--
--   $$h(y)=a^\top y+c\qquad\text{for all }y\in\mathbb R^n .$$
--
--   Assumption 1 asks for strict feasibility only of the constraints whose function $g_i$ is "nonlinear"; this predicate makes that precise as "not affine".
--
--   **Formalization Note** `Fin n → ℝ` with the pairing $a^\top y=\sum_j a_jy_j$.
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), Assumption 1, p.1795 ("for which g_i is nonlinear")

import Mathlib

namespace DualTwoStageRO

/-- **Affine function** `ℝⁿ → ℝ`: `h(y) = aᵀy + c` for some `a ∈ ℝⁿ`, `c ∈ ℝ`.
Used to read "for all i = 1,…,m1 for which g_i is nonlinear" in Assumption 1 (de Ruiter, Zhen,
den Hertog, Operations Research 71(5), 2023, p.1795) as "for which g_i is not affine".

**Formalization Note.** "Nonlinear" is read as "not affine": an affine `g_i` then needs only
feasibility, not strict feasibility, which is the weaker hypothesis (refined Slater condition). -/
def IsAffineFun {n : ℕ} (h : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ y, h y = a ⬝ᵥ y + c

end DualTwoStageRO


