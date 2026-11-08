-- Prove2me | Definitions.Def_SampleRemoval_feasible
-- name    : SampleRemoval_feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:10:28.063333+00:00
-- url     : https://prove2.me/theorems/6811e679-50b8-4eb7-a9c9-85c3e53df3aa
-- title:
--   Feasible weights $\mathcal W=\{w\in[0,1]^n: G(w)\succ0,\ \langle e,\beta(w)\rangle\le\theta\}$
-- statement:
--   Fix observations $(x_i,y_i)\in\mathbb R^d\times\mathbb R$, $i\in[n]$, and a pair $(e,\theta)\in\mathbb R^d\times\mathbb R$. The **feasible weights** of the audit are
--
--   $$
--   \mathcal W=\{\,w\in[0,1]^n:\ G(w)\succ0,\ \langle e,\beta(w)\rangle\le\theta\,\}.
--   $$
--
--   A weight vector is feasible when its least-squares fit is well defined and the linear functional $\langle e,\beta\rangle$ of the fit has been brought down to the threshold $\theta$. Integral feasible weights $\mathbf 1_S\in\mathcal W$ are the subsets $S$ whose retention (equivalently, the removal of the complement) makes the audit succeed; for instance $(e,\theta)=(e_j,0)$ asks for a sign reversal of coefficient $j$.
--
--   **Formalization Note** $G(w)\succ0$ is Mathlib's `Matrix.PosDef`; keeping it in the set also ensures that the estimate is the paper's $\beta(w)$ rather than the value $0$ of the total inverse. The set is defined for every pair $(e,\theta)$; the paper's condition that $(e,\theta)$ is a target is the separate predicate `IsTarget`.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), §2, Audits, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_SampleRemoval_gram
import Definitions.Def_SampleRemoval_ols

set_option autoImplicit false

open Matrix

namespace SampleRemoval

/-- The feasible weights of an audit with target `(e, θ) ∈ ℝᵈ × ℝ`
(Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), §2, "Audits", p.3):
`𝒲 = {w ∈ [0, 1]ⁿ : G(w) ≻ 0, ⟨e, β(w)⟩ ≤ θ}`.

**Formalization Note** `G(w) ≻ 0` is Mathlib's `Matrix.PosDef`. It is a conjunct of the set
exactly as on the page; it also guarantees that `ols x y w` is the paper's `β(w)` and not the
value `0` of Mathlib's total inverse on a singular matrix. The set is defined for every
`(e, θ)`; the paper's standing requirement `⟨e, β([n])⟩ > θ` is the separate predicate
`IsTarget`. -/
def feasible {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ) (θ : ℝ) :
    Set (Fin n → ℝ) :=
  {w | (∀ i, w i ∈ Set.Icc (0 : ℝ) 1) ∧ (gram x w).PosDef ∧ e ⬝ᵥ ols x y w ≤ θ}

end SampleRemoval


