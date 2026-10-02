-- Prove2me | Definitions.Def_LeblSCV_Varieties_regularPoints
-- name    : LeblSCV_Varieties_regularPoints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:09:00.651213+00:00
-- url     : https://prove2.me/theorems/e981479f-fe94-4d05-87fd-68d41d232cfc
-- title:
--   Definition 6.5.5 — the set $X_{\mathrm{reg}}$ of regular points
-- statement:
--   For $X \subset \mathbb{C}^n$, the set of **regular points** is
--   $$X_{\mathrm{reg}} = \{ p \in X : p \text{ is a regular point of } X \text{ of dimension } k \text{ for some } k \in \{0, \dots, n\} \}.$$
--
--   **Formalization Note.** $k$ ranges over `ℕ`; the constraint $k \le n$ is built into the regular-point definition through the coordinate split.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 185, Definition 6.5.5

import Mathlib
import Definitions.Def_LeblSCV_Varieties_IsRegularPointOfDim

namespace LeblSCV.Varieties

/-- Lebl, Definition 6.5.5: `X_reg`, the set of regular points of `X` (of any dimension
`k = 0, 1, …, n`). -/
def regularPoints {n : ℕ} (X : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {p | ∃ k : ℕ, IsRegularPointOfDim X p k}

end LeblSCV.Varieties


