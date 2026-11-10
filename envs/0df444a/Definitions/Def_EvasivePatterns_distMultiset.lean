-- Prove2me | Definitions.Def_EvasivePatterns_distMultiset
-- name    : EvasivePatterns_distMultiset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:16.913521+00:00
-- url     : https://prove2.me/theorems/7f6846f0-de32-4e51-bd58-2ef7697ceffd
-- title:
--   Distance multiset $\mathcal D(A)$ of a finite integer set
-- statement:
--   For a finite set $A \subseteq \mathbb Z$, the **distance multiset** $\mathcal D(A)$ is the multiset of positive differences $y - x$ over all pairs $x < y$ in $A$, with multiplicities (each unordered pair counted once). Two sets are **homometric** when they have the same distance multiset. For example $\mathcal D(\{0,2,4,5\}) = \{1,2,2,3,4,5\}$, and $\{0,1,3,5\}$ is homometric to $\{0,2,4,5\}$.
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §2, p.2 (PDF p.3), lines 67–68; Appendix A, p.11 (PDF p.12), line 352

import Mathlib

namespace EvasivePatterns

/-- **The distance multiset `D(A)`** of a finite integer set: the multiset of its positive pairwise
differences, with multiplicities (each unordered pair counted once).

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §2, printed p. 2 (PDF p. 3), lines 67–68: "For a finite integer set
A, let D(A) denote the multiset of its positive pairwise differences, with multiplicities."; and
Appendix A, printed p. 11 (PDF p. 12), line 352: "distances count unordered pairs with their
multiplicities".

**Formalization Note** `D(A)` is the image, as a `Multiset ℤ`, of `(x, y) ↦ y − x` over the pairs
`x < y` of `A`. Two sets are homometric when their distance multisets are equal. -/
def distMultiset (A : Finset ℤ) : Multiset ℤ :=
  ((A ×ˢ A).filter (fun x => x.1 < x.2)).val.map (fun x => x.2 - x.1)

end EvasivePatterns


