-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsFourierExpansionHolomorphicTube
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsFourierExpansionHolomorphicTube
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:45.258087+00:00
-- url     : https://prove2.me/theorems/8ca54ea2-35a4-4904-99e9-1b3220df269f
-- title:
--   Exists Fourier Expansion Holomorphic Tube
-- statement:
--   Definitions and structural lemmas for Exists Fourier Expansion Holomorphic Tube, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsFourierExpansionHolomorphicTube.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory
open MeasureTheory
end GlobalTheory


