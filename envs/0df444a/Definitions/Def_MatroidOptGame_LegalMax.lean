-- Prove2me | Definitions.Def_MatroidOptGame_LegalMax
-- name    : MatroidOptGame_LegalMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:55:59.672774+00:00
-- url     : https://prove2.me/theorems/8c9e1ea5-fa7a-4a39-b248-603340545b2f
-- title:
--   Legal MAX strategy
-- statement:
--   A strategy $c$ is a **legal MAX strategy** if at every live position where MAX is to move (even length) it names a legal move, i.e. an element not yet played.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3

import Mathlib
import Definitions.Def_MatroidOptGame_Live
import Definitions.Def_MatroidOptGame_LegalMove
import Definitions.Def_MatroidOptGame_Strategy

namespace MatroidOptGame

/-- `c` is a legal MAX strategy: at every live position of even length it names a legal move.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3. -/
def LegalMax {α : Type*} [DecidableEq α] (M : Matroid α) (c : Strategy α) : Prop :=
  ∀ h : List α, Live M h → h.length % 2 = 0 → ∃ e, c h = some e ∧ LegalMove M h e

end MatroidOptGame


