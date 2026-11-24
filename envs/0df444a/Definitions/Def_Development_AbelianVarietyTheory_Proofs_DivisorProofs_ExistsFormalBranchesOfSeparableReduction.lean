-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReduction
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReduction
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:16:55.500255+00:00
-- url     : https://prove2.me/theorems/223f061b-ca17-43b4-9988-c7ab5241be54
-- title:
--   Exists Formal Branches Of Separable Reduction
-- statement:
--   Definitions and structural lemmas for Exists Formal Branches Of Separable Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormalBranchesOfSeparableReduction.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsOfSeparableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory.ShiftHomomorphism
noncomputable def shiftHom (D : ℕ) (c : Fin D → ℂ) :
    MvPolynomial (Fin D) ℂ →ₐ[ℂ] MvPowerSeries (Fin D) ℂ :=
  MvPolynomial.aeval (fun i => MvPowerSeries.X i + MvPowerSeries.C (c i))
end GlobalTheory.ShiftHomomorphism
namespace GlobalTheory
end GlobalTheory


