-- Prove2me | Definitions.Def_SATotalCoeffLB_QForm
-- name    : SATotalCoeffLB_QForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:10.561641+00:00
-- url     : https://prove2.me/theorems/3d2255a7-ae9a-430a-b083-a64896e57c1a
-- title:
--   Quadratic forms $Q_n$ over $\mathbb F_2$
-- statement:
--   The space of quadratic forms without diagonal terms is
--
--   $$
--   Q_n = \Bigl\{ \sum_{1 \le i < j \le n} a_{ij}\, \bar x_i \bar x_j : a_{ij} \in \mathbb F_2 \Bigr\},
--   $$
--
--   an $\mathbb F_2$-vector space of dimension $\binom n2$. A form is stored by its coefficient vector $(a_{ij})_{i<j}$. A pair $e = \{i,j\}$ is identified with the form $\bar x_i \bar x_j$, i.e. with the vector having a single $1$ at $e$. In Section 9.2 the forms also index the monomials $Y^b = \prod_{i<j: b_{ij}=1} Y_{ij}$.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Section 9.1, Quadratic Forms, p.50

import Mathlib
import Definitions.Def_SATotalCoeffLB_Pair

namespace SATotalCoeffLB

/-- **The space `Q_n` of quadratic forms** `∑_{1≤i<j≤n} a_ij x̄_i x̄_j` with `a_ij ∈ F₂` (Section 9.1,
p.50, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)), stored by its coefficient vector `(a_ij)_{i<j}`. It is an `F₂`-vector space
under coefficientwise addition. A pair `e = {i, j}` is identified with the form `x̄_i x̄_j` (p.51),
i.e. with the indicator vector of `e`. -/
abbrev QForm (n : ℕ) : Type := Pair n → ZMod 2

end SATotalCoeffLB


