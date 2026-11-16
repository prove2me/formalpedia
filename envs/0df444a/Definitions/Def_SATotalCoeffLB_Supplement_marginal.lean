-- Prove2me | Definitions.Def_SATotalCoeffLB_Supplement_marginal
-- name    : SATotalCoeffLB_Supplement_marginal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:26:32.20221+00:00
-- url     : https://prove2.me/theorems/e2def67b-964d-4e4c-badd-b4007cbd8609
-- title:
--   Marginal $(D_S)|_T$ of a local distribution
-- statement:
--   Let $S$ be a finite set of coordinates, $T \subseteq S$, and let $D_S$ be a distribution over assignments $a : S \to A$ (for the paper, $A = \{0,1\}$). The **marginal** $(D_S)|_T$ is the distribution of the restriction $a|_T$ when $a \sim D_S$:
--
--   $$
--   (D_S)|_T(b) = \Pr_{a \sim D_S}\bigl[a|_T = b\bigr], \qquad b \in A^T .
--   $$
--
--   **Formalization Note** Assignments to $S$ are functions on the subtype of elements of $S$; the marginal is the push-forward of $D_S$ along restriction.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), §4.2 (Non-signaling Strategy), p.25

import Mathlib

namespace SATotalCoeffLB.Supplement

/-- **The marginal `(D_S)|_T`** of a distribution `D_S` on assignments `S → A` to the sub-set
`T ⊆ S`: the law of the restriction `a ↦ a|_T` (§4.2, p.25, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)).

**Formalization Note** Assignments to a finite set `S` of coordinates are functions on the
subtype `↥S`; the marginal is the push-forward (`PMF.map`) along restriction. -/
noncomputable def marginal {U A : Type*} {T S : Finset U} (hTS : T ⊆ S) (D : PMF (↥S → A)) :
    PMF (↥T → A) :=
  D.map (fun a t => a ⟨t.1, hTS t.2⟩)

end SATotalCoeffLB.Supplement


