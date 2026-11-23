-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:01.327363+00:00
-- url     : https://prove2.me/theorems/0e835ec8-09d7-4bef-ac71-733aea81f512
-- title:
--   Exhaust Statement Pf B
-- statement:
--   Definitions and structural lemmas for Exhaust Statement Pf B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustStatementPfB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
variable {f p q N' : ℕ}
def dk (w : V (nD f p q)) (k : Fin f) : ℝ := (1 - Zof w k * (Zof w k)ᴴ).det.re
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
variable {f p q N' : ℕ}
def dkC (k : Fin f) (v : V (nD f p q + N')) : ℂ :=
  (1 - Zof (zPart v) k * (Zof (zPart v) k)ᴴ).det
def Hh (W : V (nD f p q)) (v : V (nD f p q + N')) : ℂ :=
  ∏ k, (1 - Zof (zPart v) k * (Zof W k)ᴴ).det
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD


