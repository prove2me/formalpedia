-- Prove2me | Definitions.Def_L0BnB_Relax_Lset
-- name    : L0BnB_Relax_Lset
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:46:08.201043+00:00
-- url     : https://prove2.me/theorems/fa5b6373-505a-45a5-96b9-9194fb638c7a
-- title:
--   The set $\mathcal L(M)$ of (9)
-- statement:
--   With $X$, $y$, $\lambda_0$ fixed and $M\in\mathbb R$,
--
--   $$\mathcal L(M)=\{\lambda_2>0\ :\ \exists\,\beta\in\mathcal S(\lambda_2)\text{ with }\|\beta\|_\infty\le M\}.$$
--
--   It collects the ridge parameters for which some optimal $\beta$ of the PR$(\infty)$ relaxation lies in the Big-M box; it is the hypothesis of the second half (11) of Proposition 2.
--
--   **Formalization Note** $\|\beta\|_\infty\le M$ is written coordinatewise, $|\beta_i|\le M$ for all $i$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, eq. (9), p. 7

import Mathlib
import Definitions.Def_L0BnB_Relax_solSet

namespace L0BnB.Relax

/-- **The set `L(M)` of (9).**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, eq. (9), p. 7: "`L(M) := {λ2 > 0 | ∃β ∈ S(λ2) s.t. ‖β‖∞ ≤ M}`".

`Lset X y lam0 M = {λ₂ | 0 < λ₂ ∧ ∃ β ∈ S(λ₂), ∀ i, |βᵢ| ≤ M}`, with `X, y, λ₀` fixed.

**Formalization Note.** `‖β‖∞ ≤ M` is written as `∀ i, |β i| ≤ M` (paper.md Reading 5). -/
def Lset {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 M : ℝ) : Set ℝ :=
  {lam2 | 0 < lam2 ∧ ∃ β ∈ solSet X y lam0 lam2, ∀ i, |β i| ≤ M}

end L0BnB.Relax


