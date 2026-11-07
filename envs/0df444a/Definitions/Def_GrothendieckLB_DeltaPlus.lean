-- Prove2me | Definitions.Def_GrothendieckLB_DeltaPlus
-- name    : GrothendieckLB_DeltaPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:48:31.579508+00:00
-- url     : https://prove2.me/theorems/98bb60f6-eb5a-44d1-9758-beacdeab3652
-- title:
--   $\Delta_+(x)$
-- statement:
--   The positive part $\Delta_+(x):=\max\{\Delta(x),0\}$ of $\Delta$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.3, p.34

import Mathlib
import Definitions.Def_GrothendieckLB_Delta

namespace GrothendieckLB

/-- `Δ₊(x) := max{Δ(x), 0}` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.3, p.34). -/
noncomputable def DeltaPlus (x : ℝ) : ℝ :=
  max (Delta x) 0

end GrothendieckLB


