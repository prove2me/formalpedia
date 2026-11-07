-- Prove2me | Definitions.Def_GrothendieckLB_disagreePart
-- name    : GrothendieckLB_disagreePart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:30.757333+00:00
-- url     : https://prove2.me/theorems/7ee1bda8-2bb1-4b95-9d9a-2472e7145b52
-- title:
--   Disagreement part $k=(f-g)/2$
-- statement:
--   For functions $f,g$, the **disagreement part** is $k=(f-g)/2$. For sign functions, $k\in\{-1,0,1\}$, $hk=0$ and $h^2+k^2=1$, with $h$ the agreement part.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.1, p.32

import Mathlib

namespace GrothendieckLB

/-- The disagreement part `k = (f − g)/2` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.1, p.32). -/
noncomputable def disagreePart {α : Type*} (f g : α → ℝ) : α → ℝ :=
  fun x => (f x - g x) / 2

end GrothendieckLB


