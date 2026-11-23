-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CellSumOfCntBasic
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CellSumOfCntBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:47.313826+00:00
-- url     : https://prove2.me/theorems/d13bc632-4390-448e-b9db-59e1b733c132
-- title:
--   Cell Sum Of Cnt Basic
-- statement:
--   Definitions and structural lemmas for Cell Sum Of Cnt Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CellSumOfCntBasic.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
namespace GlobalTheory.CompanionTheory.CellSumProof
noncomputable def hits (X : Ctx) (S : Set X.G) (x : X.G) : ℝ≥0∞ :=
  ∑' γ : X.Γ, S.indicator 1 ((γ : X.G) * x)
end GlobalTheory.CompanionTheory.CellSumProof


