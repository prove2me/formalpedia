-- Prove2me | Definitions.Def_SampleRemoval_IsTarget
-- name    : SampleRemoval_IsTarget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:10:39.249005+00:00
-- url     : https://prove2.me/theorems/f791fd53-557c-46b0-92f1-58eaff4c9dc8
-- title:
--   Audit target: $\langle e,\beta([n])\rangle>\theta$
-- statement:
--   A **target** is a pair $(e,\theta)\in\mathbb R^d\times\mathbb R$ with
--
--   $$
--   \langle e,\beta([n])\rangle>\theta,
--   $$
--
--   where $\beta([n])$ is the least-squares fit on the full sample. The audit asks how many observations must be removed to bring $\langle e,\beta\rangle$ to at most $\theta$. Reversing the sign of a positive coefficient $\beta_j([n])$ is the target $(e_j,0)$.
--
--   **Formalization Note** $\beta([n])$ is the estimate at the all-ones weight. If the full-sample Gram matrix is singular, the total inverse gives $\beta([n])=0$ and the predicate reads $\theta<0$; under general position with $n\ge d$ the full-sample Gram matrix is positive definite.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), §2, Audits, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_SampleRemoval_ols

set_option autoImplicit false

open Matrix

namespace SampleRemoval

/-- A target is a pair `(e, θ) ∈ ℝᵈ × ℝ` with `⟨e, β([n])⟩ > θ` (Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), §2, "Audits", p.3):
on the full sample the linear functional `⟨e, β⟩` of the least-squares estimate lies strictly
above the threshold, and the audit asks how much must be removed to bring it to `≤ θ`.

**Formalization Note** `β([n]) = β(1_{[n]})` is `ols x y (fun _ => 1)`. If `G(1)` is singular
(possible only when the design does not span `ℝᵈ`), Mathlib's total inverse gives
`ols x y 1 = 0` and the predicate reads `θ < 0`; under general position with `n ≥ d`, `G(1)`
is positive definite. -/
def IsTarget {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ) (θ : ℝ) :
    Prop :=
  θ < e ⬝ᵥ ols x y (fun _ => 1)

end SampleRemoval


