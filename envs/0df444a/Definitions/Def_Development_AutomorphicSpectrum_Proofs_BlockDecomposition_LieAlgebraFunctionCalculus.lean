-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraFunctionCalculus
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraFunctionCalculus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:20.192789+00:00
-- url     : https://prove2.me/theorems/3539a3a9-94c6-4952-9b75-ef3dd63aec1f
-- title:
--   Lie Algebra Function Calculus
-- statement:
--   Definitions and structural lemmas for Lie Algebra Function Calculus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraFunctionCalculus.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
namespace GlobalTheory.CompanionTheory.AdProj
noncomputable def entryMul {n : ℕ} (h : Fin n → ℝ) (g : ℝ → ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (g (h i - h j) : ℂ) * X i j
end GlobalTheory.CompanionTheory.AdProj


