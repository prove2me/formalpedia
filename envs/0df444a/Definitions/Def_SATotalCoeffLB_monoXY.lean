-- Prove2me | Definitions.Def_SATotalCoeffLB_monoXY
-- name    : SATotalCoeffLB_monoXY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:06.992416+00:00
-- url     : https://prove2.me/theorems/78d32704-a575-4f89-8fd3-0afef64beaa3
-- title:
--   Monomial $X^\alpha Y^b$
-- statement:
--   For $\alpha \in \mathbb F_2^n$ and $b \in Q_n$, the monomial in the variables $X, Y$ is
--
--   $$
--   X^\alpha Y^b = \prod_{i : \alpha_i = 1} X_i \prod_{i<j : b_{ij} = 1} Y_{ij},
--   $$
--
--   an element of the Boolean quotient ring $\mathbb R[X,Y]/\langle y^2-1 : y \in X \cup Y\rangle$. Every monomial in $X, Y$ is $X^\alpha Y^b$ for a unique $\alpha$ and $b$; for $\lambda \in Q_n$, $Y^\lambda = X^0 Y^\lambda$.
--
--   **Formalization Note** The variables are $X \sqcup Y$, with $X_i$ and $Y_e$ the two injections.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Section 9.2, p.52

import Mathlib
import Definitions.Def_SATotalCoeffLB_var
import Definitions.Def_SATotalCoeffLB_QForm

namespace SATotalCoeffLB

/-- **The monomial `X^α Y^b`** in the variables `X, Y` (Section 9.2, p.52, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)):
`X^α := ∏_{i : α_i = 1} X_i` for `α ∈ F₂ⁿ` and `Y^b := ∏_{i<j : b_ij = 1} Y_{ij}` for `b ∈ Q_n`. Every
monomial in `X, Y` is `X^α Y^b` for a unique `α` and `b` (p.52). The variables `X, Y` are
`Fin n ⊕ Pair n` (`X_i = Sum.inl i`, `Y_e = Sum.inr e`). -/
noncomputable def monoXY {n : ℕ} (α : Fin n → ZMod 2) (b : QForm n) : CubeFn (Fin n ⊕ Pair n) :=
  fun x => (∏ i : Fin n, if α i = 1 then var (Sum.inl i : Fin n ⊕ Pair n) x else 1) *
    ∏ e : Pair n, if b e = 1 then var (Sum.inr e : Fin n ⊕ Pair n) x else 1

end SATotalCoeffLB


