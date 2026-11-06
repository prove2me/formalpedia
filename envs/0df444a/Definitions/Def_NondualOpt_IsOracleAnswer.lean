-- Prove2me | Definitions.Def_NondualOpt_IsOracleAnswer
-- name    : NondualOpt_IsOracleAnswer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:52.858376+00:00
-- url     : https://prove2.me/theorems/59c17b57-aaf3-4d19-8c95-e281bdae4e77
-- title:
--   A valid oracle answer: $g\in\partial f(x)\cap B_{q^*}^d$ relative to $B_p^d$
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$, $x\in\mathbb R^d$ and $q^*$ the conjugate exponent of $q$. A vector $g\in\mathbb R^d$ is a **valid subgradient answer** at the query $x$ for the feasible set $X=B_p^d$ and the subgradient set $H=B_{q^*}^d$ if
--   $$
--   \|g\|_{q^*}\le1\qquad\text{and}\qquad f(y)\ge f(x)+\langle g,y-x\rangle\quad\text{for all }y\in B_p^d .
--   $$
--   This is the paper's oracle requirement "$g\in\partial f(x)\cap H$ in the sense of (3)", with the subgradient inequality (3) taken relative to the feasible set.
--
--   **Formalization Note** `qs` stands for $q^*$; every statement using this predicate assumes $q^{-1}+q_*^{-1}=1$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, §2, (3), p.7

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM
import Definitions.Def_NondualOpt_lpBall

open scoped ENNReal

namespace NondualOpt

/-- A valid subgradient answer of the first-order oracle at a query `x`, for the feasible set
`X = B_p^d` and the subgradient set `H = B_{q∗}^d`: `‖g‖_{q∗} ≤ 1` and
`f(y) ≥ f(x) + ⟨g, y − x⟩` for every `y ∈ B_p^d`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, §2, (3) and "the oracle returns the value
`f(x)` and a subgradient `g ∈ ∂f(x) ∩ H` in the sense of (3)", p.7.

**Formalization Note.** `qs` is the conjugate exponent `q∗` (every use assumes `q⁻¹ + qs⁻¹ = 1`).
The subgradient inequality is required on the feasible set only, as in (3). -/
def IsOracleAnswer {d : ℕ} (p qs : ℝ≥0∞) (f : (Fin d → ℝ) → ℝ) (x g : Fin d → ℝ) : Prop :=
  RegimeDRCVaR.normM qs g ≤ 1 ∧ ∀ y ∈ lpBall p d, f x + dotProduct g (y - x) ≤ f y

end NondualOpt


