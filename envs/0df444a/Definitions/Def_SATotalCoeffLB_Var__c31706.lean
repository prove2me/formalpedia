-- Prove2me | Definitions.Def_SATotalCoeffLB_Var__c31706
-- name    : SATotalCoeffLB_Var
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:15.291125+00:00
-- url     : https://prove2.me/theorems/c3170617-b15e-4efd-b28e-0c4f5455f8b7
-- title:
--   The variables $X$, $Y$, $T$
-- statement:
--   The system of Theorem 3 has three groups of variables: the inputs $X_1, \dots, X_n$; one variable $Y_e = Y_{ij}$ for each pair $e = \{i,j\}$, $i<j$; and the check variables $T_1, \dots, T_t$. The variable set is their disjoint union $X \sqcup Y \sqcup T$, of size $n + \binom n2 + t$.
--
--   **Formalization Note** Indices are $0$-based. $X_i$, $Y_e$, $T_\ell$ are the three injections into the disjoint union.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.9 (AND gate checks, parity checks), Section 9, p.48

import Mathlib
import Definitions.Def_SATotalCoeffLB_Pair

namespace SATotalCoeffLB

/-- **The variables `X, Y, T`** of the system of Theorem 3 (p.9; Section 9, p.48) of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178):
`X_1, …, X_n` (`Sum.inl i`), one `Y_e` for every pair `e = {i, j}`, `i < j` (`Sum.inr (Sum.inl e)`),
and the check variables `T_1, …, T_t` (`Sum.inr (Sum.inr ℓ)`).

**Formalization Note** Indices are 0-based (`Fin n`, `Fin t`). -/
abbrev Var (n t : ℕ) : Type := Fin n ⊕ Pair n ⊕ Fin t

end SATotalCoeffLB


