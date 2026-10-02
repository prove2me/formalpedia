-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_IsRelCompactIn
-- name    : LeblSCV_Pseudoconvex_IsRelCompactIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:33:56.130919+00:00
-- url     : https://prove2.me/theorems/a104e785-7856-4989-b9b3-d43b4e06e004
-- title:
--   Relatively compact subset $K \subset\subset U$
-- statement:
--   Let $X$ be a topological space and $K, U \subset X$. We write $K \subset\subset U$, and say that $K$ is **relatively compact** in $U$, if the closure of $K$ in the subspace topology of $U$ is compact. When $X$ is Hausdorff, this holds exactly when the closure $\overline{K}$ of $K$ in $X$ is compact and contained in $U$:
--   $$K \subset\subset U \iff \overline{K} \text{ is compact and } \overline{K} \subset U.$$
--
--   The notation is used throughout the chapter: for hulls, for exhaustion functions, and in the continuity principle.
--
--   **Formalization Note.** The definition uses the second (ambient-closure) form. It is equivalent to the subspace-closure form in Hausdorff spaces, which covers every space in this mission.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 33 (notation ⊂⊂ after Definition 1.4.3) and footnote on p. 90

import Mathlib

namespace LeblSCV.Pseudoconvex

/-- `K ⊂⊂ U` (Lebl, p. 33 and footnote on p. 90): `K` is a relatively compact subset of `U`, i.e.
the closure of `K` in the subspace topology of `U` is compact. In a Hausdorff space this is the
same as: the (ambient) closure of `K` is compact and contained in `U`, which is the form used here. -/
def IsRelCompactIn {X : Type*} [TopologicalSpace X] (K U : Set X) : Prop :=
  IsCompact (closure K) ∧ closure K ⊆ U

end LeblSCV.Pseudoconvex


