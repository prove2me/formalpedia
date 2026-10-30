-- Prove2me | Definitions.Def_L0BnB_Relax_solSet
-- name    : L0BnB_Relax_solSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:45:27.471995+00:00
-- url     : https://prove2.me/theorems/30bd66b9-739d-44ce-bdff-c8d1587d18e3
-- title:
--   $\mathcal S(\lambda_2)$: optimal $\beta$'s of the PR(∞) relaxation
-- statement:
--   With $X$, $y$, $\lambda_0$ fixed, $\mathcal S(\lambda_2)\subseteq\mathbb R^p$ is the set of optimal solutions (in $\beta$) of the interval relaxation of PR$(\infty)$: $\beta\in\mathcal S(\lambda_2)$ if and only if there are $z,s\in\mathbb R^p$ such that $(\beta,z,s)$ is feasible for that relaxation and its objective value is at most that of every feasible $(\beta',z',s')$.
--
--   **Formalization Note** The set is the $\beta$-projection of the optimal set and is written without reference to the infimum $V_{PR(\infty)}$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 7 (before eq. (9))

import Mathlib
import Definitions.Def_L0BnB_Relax_prFeasible
import Definitions.Def_L0BnB_Relax_prObj

namespace L0BnB.Relax

/-- **`S(λ₂)`, the set of optimal solutions (in β) of the interval relaxation of PR(∞).**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, p. 7: "Let `S(λ2)` be the set of optimal solutions (in β) of the interval relaxation of
PR(∞)".

`β ∈ solSet X y lam0 lam2` iff there are `z, s` such that `(β, z, s)` is feasible for the
relaxation of PR(∞) and its objective is at most that of every feasible `(β', z', s')`.

**Formalization Note.** This is the β-projection of the set of optimal solutions (paper.md
Reading 4). It is written without reference to the infimum `VPRinf`, so it carries no junk
value. The data `X, y, λ₀` are fixed and `λ₂` is the argument, as in (9). The identification
"`β̂ ∈ S(λ2)` (i.e., `β̂` is optimal for (6))" (p. 30) is a theorem of the mission. -/
def solSet {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 : ℝ) :
    Set (Fin p → ℝ) :=
  {β | ∃ z s : Fin p → ℝ, prFeasible β z s ∧
    ∀ β' z' s' : Fin p → ℝ, prFeasible β' z' s' →
      prObj X y lam0 lam2 β z s ≤ prObj X y lam0 lam2 β' z' s'}

end L0BnB.Relax


