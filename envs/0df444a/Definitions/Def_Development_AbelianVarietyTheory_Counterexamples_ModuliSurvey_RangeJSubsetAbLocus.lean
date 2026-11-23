-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_RangeJSubsetAbLocus
-- name    : Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_RangeJSubsetAbLocus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:54.577015+00:00
-- url     : https://prove2.me/theorems/66a6f273-1baf-428a-af17-3cf6f4efbd3d
-- title:
--   Range JSubset Ab Locus
-- statement:
--   Definitions and structural lemmas for Range JSubset Ab Locus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/RangeJSubsetAbLocus.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ModelScope
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
end GlobalTheory.ModelScope


