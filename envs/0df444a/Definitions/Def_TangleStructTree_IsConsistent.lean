-- Prove2me | Definitions.Def_TangleStructTree_IsConsistent
-- name    : TangleStructTree_IsConsistent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:15.882445+00:00
-- url     : https://prove2.me/theorems/95c6fe3b-46d0-49cc-842a-08a4c0b8af06
-- title:
--   Consistent sets of oriented separations
-- statement:
--   Let $(\vec S,\le,{}^*)$ be a separation system. Two oriented separations $\vec r,\vec s$ **point away from each other** if
--   $$
--   \vec r\le\overleftarrow{s}\qquad(\text{equivalently } \vec s\le\overleftarrow{r}).
--   $$
--   A set $\sigma\subseteq\vec S$ is **consistent** if no two of its elements $\vec r,\vec s$ with $r\neq s$ point away from each other; here $r\ne s$ compares the underlying unoriented separations.
--
--   Consistency is the basic axiom of tangles: an orientation of a graph's separations that points two separations away from each other cannot describe a single highly connected region.
--
--   **Formalization Note** $r\ne s$ is encoded as $y\ne x$ and $y\ne x^*$. The order is the paper's, which is the inverse of the order used in Diestel's *Abstract separation systems* (paper's footnote 5); the paper itself reads "point away from each other" as $\vec s<\overleftarrow{t}$ in the proof of its Lemma 2.2. A consistent set may contain both orientations of a separation.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §2, p.4 (PDF 15)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem

namespace TangleStructTree

open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- A subset of `S⃗` is **consistent** if no pair of its elements `r⃗, s⃗` with `r ≠ s` point away
from each other (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §2, p.4 (PDF 15)).

**Formalization Note**
1. "`r ≠ s`" compares the underlying unoriented separations `{r⃗, r⃖} ≠ {s⃗, s⃖}`, i.e.
   `y ≠ x` and `y ≠ x∗`.
2. "`r⃗` and `s⃗` point away from each other" is `r⃗ ≤ s⃖` (equivalently `s⃗ ≤ r⃖`). This is the
   paper's order, the inverse of the order of its reference [9] (footnote 5); the paper uses it
   in this form in the proof of Lemma 2.2 ("`s⃗ < r⃖ < t⃖`, that is `s⃗` and `t⃗` point away from each
   other") and in the closure identity on p.4.
3. A consistent set may contain both orientations of a separation; consistency does not forbid it. -/
def IsConsistent (σ : Set E) : Prop :=
  ∀ x ∈ σ, ∀ y ∈ σ, y ≠ x → y ≠ rev x → ¬ x ≤ rev y

end TangleStructTree


