-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JhMultMulLeOfSteps
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JhMultMulLeOfSteps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:13.020167+00:00
-- url     : https://prove2.me/theorems/18b4a59c-104a-4d06-9548-fb646aa43352
-- title:
--   Jh Mult Mul Le Of Steps
-- statement:
--   Definitions and structural lemmas for Jh Mult Mul Le Of Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JhMultMulLeOfSteps.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JHMult
namespace GlobalTheory.CompanionTheory.CsStages
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
end GlobalTheory.CompanionTheory.CsStages


