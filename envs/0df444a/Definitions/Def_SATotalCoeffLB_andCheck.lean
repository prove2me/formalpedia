-- Prove2me | Definitions.Def_SATotalCoeffLB_andCheck
-- name    : SATotalCoeffLB_andCheck
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:38.747247+00:00
-- url     : https://prove2.me/theorems/504f5f4d-ea39-44a4-b24a-5f95b0d077c4
-- title:
--   AND gate check $p_{ij} = (1 - Y_{ij}\,\omega_{ij}(X))/2$
-- statement:
--   For a pair $e = \{i,j\}$ with $i<j$, the **AND gate check** is
--
--   $$
--   p_{ij} = \frac{1 - Y_{ij}\, \omega_{ij}(X)}{2}, \qquad \omega_{ij}(X) = \frac{1 + X_i + X_j - X_iX_j}{2},
--   $$
--
--   an element of the Boolean quotient ring $\mathbb R[X, Y, T]/\langle y^2 - 1\rangle$. On the cube it equals $0$ if $Y_{ij}$ is the AND of $X_i$ and $X_j$ and $1$ otherwise. Its multilinear expansion is $\tfrac12 - \tfrac14 Y_{ij} - \tfrac14 X_iY_{ij} - \tfrac14 X_jY_{ij} + \tfrac14 X_iX_jY_{ij}$, a $3$-junta with coefficients of magnitude at most $1/2$.
--
--   **Formalization Note** The number $t$ of check variables is an explicit parameter, since $p_{ij}$ does not mention them.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.9 (AND gate checks) and p.49

import Mathlib
import Definitions.Def_SATotalCoeffLB_Var__c31706
import Definitions.Def_SATotalCoeffLB_omegaAND

namespace SATotalCoeffLB

/-- **The AND gate check** `p_ij := (1 − Y_ij ω_ij(X))/2` for a pair `e = (i, j)`, `i < j`
(p.9 and p.49 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)), as an element of the Boolean quotient ring on the variables
`X, Y, T` with `t` check variables. On the cube it is `0` if `Y_ij` is the AND of `X_i, X_j` and `1`
otherwise.

**Formalization Note** `t` is an explicit argument because `p_ij` does not mention the `T`
variables. -/
noncomputable def andCheck {n : ℕ} (t : ℕ) (e : Pair n) : CubeFn (Var n t) :=
  fun x => (1 - var (Sum.inr (Sum.inl e) : Var n t) x *
    omegaAND (Sum.inl e.1.1 : Var n t) (Sum.inl e.1.2) x) / 2

end SATotalCoeffLB


