-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetUnitIdealIntegral
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetUnitIdealIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:00.866383+00:00
-- url     : https://prove2.me/theorems/bb2e933a-70d2-4de1-9dff-371eaafcfd56
-- title:
--   Coset Unit Ideal Integral
-- statement:
--   Definitions and structural lemmas for Coset Unit Ideal Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetUnitIdealIntegral.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
namespace GlobalTheory.CompanionTheory.Equi.CosetTop
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.CompanionTheory.Equi.CosetTop
end


