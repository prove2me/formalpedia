-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableOfMulUnimodular
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableOfMulUnimodular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:36.018559+00:00
-- url     : https://prove2.me/theorems/427e7918-b7e6-4b46-b8bd-0ac363df6472
-- title:
--   Integrable Of Mul Unimodular
-- statement:
--   Definitions and structural lemmas for Integrable Of Mul Unimodular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableOfMulUnimodular.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open MeasureTheory
noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
def PosOn {n : ℕ} (ε : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ w ∈ S, w ≠ 0 → 0 < ε * (star w ⬝ᵥ Z.mulVec w).re
def NonnegOn {n : ℕ} (ε : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ w ∈ S, 0 ≤ ε * (star w ⬝ᵥ Z.mulVec w).re
end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame


