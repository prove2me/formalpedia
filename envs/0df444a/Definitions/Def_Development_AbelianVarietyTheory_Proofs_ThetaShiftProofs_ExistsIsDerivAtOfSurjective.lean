-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsDerivAtOfSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsDerivAtOfSurjective
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T13:44:55.686093+00:00
-- url     : https://prove2.me/theorems/88cd2283-cf52-5e4f-95ce-fbbe3edb5948
-- title:
--   Exists Is Deriv At Of Surjective
-- statement:
--   Definitions and structural lemmas for Exists Is Deriv At Of Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsDerivAtOfSurjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HolDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
noncomputable section
namespace GlobalTheory.HolHomOnto
open GlobalTheory.TangentOrigin GlobalTheory.HolHom
end GlobalTheory.HolHomOnto


