-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmoothLogMemLieAlg
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmoothLogMemLieAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:10:28.109929+00:00
-- url     : https://prove2.me/theorems/97e1c27f-462a-48ba-9070-7c1374f02078
-- title:
--   Exists Smooth Log Mem Lie Alg
-- statement:
--   Definitions and structural lemmas for Exists Smooth Log Mem Lie Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmoothLogMemLieAlg.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtExpMulExpOfFiniteDimensional
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmoothLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace GlobalTheory.CompanionTheory.ClosedSubgroup
section Banach
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
end Banach
end GlobalTheory.CompanionTheory.ClosedSubgroup


