-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCharacterSeparatingLattice
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCharacterSeparatingLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:48.908522+00:00
-- url     : https://prove2.me/theorems/e17abb7c-09e6-4742-9465-6597f165f9f9
-- title:
--   Exists Character Separating Lattice
-- statement:
--   Definitions and structural lemmas for Exists Character Separating Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCharacterSeparatingLattice.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
noncomputable section
namespace GlobalTheory.CompanionTheory.CharacterBiduality
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.CompanionTheory.CharacterBiduality


