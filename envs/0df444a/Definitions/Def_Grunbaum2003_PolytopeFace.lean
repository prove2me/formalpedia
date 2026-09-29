-- Prove2me | Definitions.Def_Grunbaum2003_PolytopeFace
-- name    : Grunbaum2003_PolytopeFace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:34:44.273447+00:00
-- url     : https://prove2.me/theorems/0020354e-43a9-4944-a711-9894241385fa
-- title:
--   Faces under the exposed-face convention
-- statement:
--   An exposed face of a subset of real coordinate space, including the empty face and the entire body.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §2.4, printed p. 17 / PDF p. 35; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Hom.Basic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

/-- All exposed faces of a body, including the empty and full faces.
Source convention: §2.4, printed p. 17 / PDF p. 35. -/
abbrev PolytopeFace {d : ℕ} (P : Set (Fin d → ℝ)) :=
  {F : Set (Fin d → ℝ) // IsExposed ℝ P F}

end Grunbaum2003


