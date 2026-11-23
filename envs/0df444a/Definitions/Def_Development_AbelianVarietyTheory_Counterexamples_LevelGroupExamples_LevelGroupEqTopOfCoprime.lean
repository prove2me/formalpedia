-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_LevelGroupEqTopOfCoprime
-- name    : Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_LevelGroupEqTopOfCoprime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:47.168351+00:00
-- url     : https://prove2.me/theorems/5307dfd9-e85c-4a0c-9828-ffed0ddac978
-- title:
--   Level Group Eq Top Of Coprime
-- statement:
--   Definitions and structural lemmas for Level Group Eq Top Of Coprime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/LevelGroupEqTopOfCoprime.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LevelGroupTest
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
end GlobalTheory.LevelGroupTest


