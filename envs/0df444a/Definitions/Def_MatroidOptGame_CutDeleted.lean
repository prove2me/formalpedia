-- Prove2me | Definitions.Def_MatroidOptGame_CutDeleted
-- name    : MatroidOptGame_CutDeleted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:53.327265+00:00
-- url     : https://prove2.me/theorems/698b5276-6516-460d-94ff-37a1911bcb8f
-- title:
--   MAX's deletions include a cut
-- statement:
--   After history $h$, **MAX's deletions include a cut** of $M$ if some cocircuit $K$ of $M$ (a cut: an inclusion-minimal set meeting every base) satisfies $K \subseteq C$, where $C$ is the set of elements MAX has deleted. Then no base of $M$ avoids $C$, so MIN can no longer complete a base, and the game ends with payoff $\infty$.
--
--   **Formalization Note** "$C$ includes a cut" is read as containment of a cocircuit, not as $C$ itself being a cocircuit.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 (end of the game); Appendix A, pp.19–20 (cuts are cocircuits)

import Mathlib
import Definitions.Def_MatroidOptGame_maxSet

namespace MatroidOptGame

/-- The elements MAX has deleted in history `h` include a cut of `M`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 ("The game ends if the set C_j … of elements played so far by
MAX includes a cut in M"); a cut is a cocircuit, p.19–20 ("A cocircuit (or cut) of M is a circuit
in the dual matroid", "a cut … is an inclusion-wise minimal set of elements that intersects every
base of M").

**Formalization Note.** "Includes a cut" is read as containment: some cocircuit `K` of `M`
satisfies `K ⊆ C`, not that `C` itself is a cocircuit. -/
def CutDeleted {α : Type*} [DecidableEq α] (M : Matroid α) (h : List α) : Prop :=
  ∃ K : Set α, K ⊆ (maxSet h : Set α) ∧ M.IsCocircuit K

end MatroidOptGame


