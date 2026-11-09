-- Prove2me | Definitions.Def_MatroidOptGame_LegalMin
-- name    : MatroidOptGame_LegalMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:56:16.020351+00:00
-- url     : https://prove2.me/theorems/9a75f8a4-7b29-4428-9853-04d820614a3d
-- title:
--   Legal MIN strategy
-- statement:
--   A strategy $s$ is a **legal MIN strategy** if at every live position where MIN is to move (odd length) it names a legal move: an element not yet played that is not a loop of the current minor (so MIN's contracted set stays independent).
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3

import Mathlib
import Definitions.Def_MatroidOptGame_Live
import Definitions.Def_MatroidOptGame_LegalMove
import Definitions.Def_MatroidOptGame_Strategy

namespace MatroidOptGame

/-- `s` is a legal MIN strategy: at every live position of odd length it names a legal move (an
unplayed non-loop of the current minor).

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 ("MIN is prohibited from selecting a loop"). -/
def LegalMin {α : Type*} [DecidableEq α] (M : Matroid α) (s : Strategy α) : Prop :=
  ∀ h : List α, Live M h → h.length % 2 = 1 → ∃ e, s h = some e ∧ LegalMove M h e

end MatroidOptGame


