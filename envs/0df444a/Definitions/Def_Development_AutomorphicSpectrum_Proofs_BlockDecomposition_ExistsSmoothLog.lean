-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmoothLog
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmoothLog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:43.766687+00:00
-- url     : https://prove2.me/theorems/6942afae-a183-4753-a349-b182d93c769c
-- title:
--   Exists Smooth Log
-- statement:
--   Definitions and structural lemmas for Exists Smooth Log, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmoothLog.lean

import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
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
namespace GlobalTheory.CompanionTheory.SmoothLog
def OpMat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ
instance (n : ℕ) : NormedRing (OpMat n) := Matrix.linftyOpNormedRing
instance (n : ℕ) : NormedAlgebra ℝ (OpMat n) := Matrix.linftyOpNormedAlgebra
instance (n : ℕ) : FiniteDimensional ℝ (OpMat n) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ))
instance (n : ℕ) : CompleteSpace (OpMat n) := FiniteDimensional.complete ℝ _
def toOp (n : ℕ) : Matrix (Fin n) (Fin n) ℂ ≃L[ℝ] OpMat n :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.refl ℝ (Matrix (Fin n) (Fin n) ℂ))
end GlobalTheory.CompanionTheory.SmoothLog


