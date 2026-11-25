-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_LieCombBaseChange
-- name    : Development_AbelianVarietyTheory_Proofs_GenericRegularity_LieCombBaseChange
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:19:36.055439+00:00
-- url     : https://prove2.me/theorems/09c647e9-42cc-5486-8e8e-11b8f32df56d
-- title:
--   Lie Comb Base Change
-- statement:
--   Definitions and structural lemmas for Lie Comb Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/LieCombBaseChange.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj
namespace GlobalTheory.LieCombBaseChange
variable {R R' : Type} [CommRing R] [CommRing R']
end GlobalTheory.LieCombBaseChange
namespace GlobalTheory
open LieCombBaseChange
end GlobalTheory


