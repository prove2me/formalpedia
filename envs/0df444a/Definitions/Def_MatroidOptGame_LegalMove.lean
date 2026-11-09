-- Prove2me | Definitions.Def_MatroidOptGame_LegalMove
-- name    : MatroidOptGame_LegalMove
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:58.18321+00:00
-- url     : https://prove2.me/theorems/0dd2800a-2c49-4b1e-8964-3f2b91d7ef21
-- title:
--   Legal move after a history
-- statement:
--   After history $h$, an element $e$ is a **legal move** for the player to move if $e$ has not been played yet (it lies in the ground set $E \setminus (C \cup S)$ of the current minor $M / S \setminus C$), and, when it is MIN's turn (odd length of $h$), $e$ is not a loop of the current minor:
--   $$
--   S \cup \{e\} \text{ is independent in } M .
--   $$
--   MAX may delete any remaining element; MIN is prohibited from contracting a loop.
--
--   **Formalization Note** Because $S$ is independent, $e$ is a non-loop of $M/S$ exactly when $S \cup \{e\}$ is independent in $M$.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3

import Mathlib
import Definitions.Def_MatroidOptGame_minSet

namespace MatroidOptGame

/-- `e` is a legal next move after history `h`. Every player plays an element not yet played
(an element of the current minor `M / S ∖ C`). If it is MIN's turn (`h` has odd length), the
element must also not be a loop of the current minor, i.e. `S ∪ {e}` is independent in `M`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 (MAX deletes `c(M_j) ∈ E_j`, MIN contracts `s(M′_j) ∈ E′_j`;
"MIN is prohibited from selecting a loop").

**Formalization Note.** The current minor after history `h` is `M / S ∖ C` with ground set
`E ∖ (C ∪ S)`; since `S` is independent, `e` is a non-loop of `M / S` exactly when
`S ∪ {e}` is independent in `M`. -/
def LegalMove {α : Type*} [DecidableEq α] (M : Matroid α) (h : List α) (e : α) : Prop :=
  e ∉ h ∧ (h.length % 2 = 1 → M.Indep (insert e (minSet h) : Set α))

end MatroidOptGame


