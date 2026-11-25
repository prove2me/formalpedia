-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_PairBdNonneg
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_PairBdNonneg
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:15:37.412027+00:00
-- url     : https://prove2.me/theorems/49508b58-e93c-4c28-80bf-932200532c92
-- title:
--   Pair Bd Nonneg
-- statement:
--   Definitions and structural lemmas for Pair Bd Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/PairBdNonneg.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.DegCnt
namespace GlobalTheory.DegAsm
def pairBd (K : Type) [Field K] [NumberField K] (k g j T x x' : ℕ) : ℝ :=
  let f : ℕ := Formalism.HermitianLatticesTheory.fDeg K
  let Mb : ℝ := (20 * (f : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * (f : ℝ) * (6 + cf K))
  let D₀ : ℝ := (T : ℝ) ^ (2 * f)
  let Y : ℝ := (x : ℝ) * x' * D₀ ^ 2
  ((x : ℝ) * x') ^ ((k : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 10 + 4 * cf K) *
    (1 + Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ f *
        (∑ s ∈ Finset.Ico 1 k, ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * Y ^ 7) ^ s) +
      ((2 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * D₀ * x * x') ^ k)
end GlobalTheory.DegAsm


