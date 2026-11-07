-- Prove2me | Definitions.Def_GrothendieckLB_agreePart
-- name    : GrothendieckLB_agreePart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:30.128099+00:00
-- url     : https://prove2.me/theorems/4286f7d5-b12c-4d67-a491-f20c21e748a6
-- title:
--   Agreement part $h=(f+g)/2$
-- statement:
--   For functions $f,g$, the **agreement part** is $h=(f+g)/2$. For sign functions, $h\in\{-1,0,1\}$, $h$ equals $f$ where $f=g$, and $h$ vanishes where $f\ne g$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.1, p.32

import Mathlib

namespace GrothendieckLB

/-- The agreement part `h = (f + g)/2` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.1, p.32). -/
noncomputable def agreePart {α : Type*} (f g : α → ℝ) : α → ℝ :=
  fun x => (f x + g x) / 2

end GrothendieckLB


