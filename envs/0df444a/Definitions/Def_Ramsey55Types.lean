-- Prove2me | Definitions.Def_Ramsey55Types
-- name    : Ramsey55Types
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:37:37.831921+00:00
-- url     : https://prove2.me/theorems/85c8b3d8-b89f-4394-9ea6-8655dd56ef4b
-- title:
--   Ramsey theory basic types
-- statement:
--   Basic types for Ramsey theory: 2-colorings and monochromaticity.
-- source:
--   Daugherty-Ward-Ryan (2026)

import Mathlib.Data.Finset.Card

namespace Ramsey55

/-- A 2-coloring of K_n edges (Red=true, Blue=false) -/
def Coloring (n : ℕ) := Fin n → Fin n → Bool

/-- Check if all edges in a set have the same color -/
def isMonochromatic {n : ℕ} (χ : Coloring n) (S : Finset (Fin n)) : Prop :=
  (∀ i ∈ S, ∀ j ∈ S, i < j → χ i j = true) ∨
  (∀ i ∈ S, ∀ j ∈ S, i < j → χ i j = false)

end Ramsey55


