-- Prove2me | Definitions.Def_MatroidOptGame_unionRank
-- name    : MatroidOptGame_unionRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:31.493076+00:00
-- url     : https://prove2.me/theorems/7724149b-2e41-4890-83b8-7beef69a5e1f
-- title:
--   Rank $r_{M\vee M}(E)$ of the union
-- statement:
--   $r_{M\vee M}(E)$ is the rank of the matroid union $M \vee M$: the maximum size of a set $I \cup J$ with $I, J$ independent in $M$.
--
--   It is at most $2\,r_M(E)$, with equality exactly when $M$ has two disjoint bases; it is the quantity that decides between the two cases in the definition of $\delta(M, w)$.
--
--   **Formalization Note** A maximum over the finitely many union-independent finite sets of a finite type; the empty set is one of them.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.1, p.4; Appendix A, pp.19–20

import Mathlib
import Definitions.Def_MatroidOptGame_UnionIndep

namespace MatroidOptGame

open Classical in
/-- `r_{M∨M}(E)`: the maximum size of a set independent in the union `M ∨ M`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.1, p.4 (the case split of `δ`), and Appendix A, p.19–20.

**Formalization Note.** A `Finset.sup` over the finitely many union-independent `Finset`s of a
finite type; `∅` is one of them, so no junk value arises. -/
noncomputable def unionRank {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α) : ℕ :=
  ((Finset.univ : Finset (Finset α)).filter (fun F => UnionIndep M F)).sup Finset.card

end MatroidOptGame


