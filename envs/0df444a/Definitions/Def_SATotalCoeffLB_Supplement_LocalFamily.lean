-- Prove2me | Definitions.Def_SATotalCoeffLB_Supplement_LocalFamily
-- name    : SATotalCoeffLB_Supplement_LocalFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:26:45.250952+00:00
-- url     : https://prove2.me/theorems/67cb671e-88b8-4d2c-b01d-490cc04af962
-- title:
--   A family $\{D_S\}_{S\subseteq U,\,|S|\le k}$ of local distributions
-- statement:
--   For a set $U$ of coordinates, an alphabet $A$ and a natural number $k$, a **family of local distributions** assigns to every set $S \subseteq U$ with $|S| \le k$ a distribution $D_S$ over assignments $S \to A$. In the paper $A = \{0,1\}$ (or $\{\pm1\}$, by the standard identification), and such a family is a candidate non-signaling strategy for a PCP of length $N$ when $U = [N]$.
--
--   **Formalization Note** The family is a dependent function of $S$ and of a proof that $|S| \le k$.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), §4.2 (Non-signaling Strategy), p.25

import Mathlib

namespace SATotalCoeffLB.Supplement

/-- **A family `{D_S}_{S ⊆ U, |S| ≤ k}` of local distributions**: for every set `S` of at most
`k` coordinates of `U`, a distribution `D_S` on assignments `S → A` (§4.2, p.25, of
Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178); there `A = {0, 1}`).

**Formalization Note** The family is a dependent function of the set `S` and of a proof of
`|S| ≤ k`; a distribution is a Mathlib `PMF`. -/
abbrev LocalFamily (U A : Type*) (k : ℕ) : Type _ :=
  (S : Finset U) → S.card ≤ k → PMF (↥S → A)

end SATotalCoeffLB.Supplement


