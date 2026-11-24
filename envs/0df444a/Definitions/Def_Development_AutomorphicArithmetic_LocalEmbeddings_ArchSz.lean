-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz
-- name    : Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:58.854795+00:00
-- url     : https://prove2.me/theorems/c64a895f-9983-4297-a955-7c7ce9f32f61
-- title:
--   Arch Sz
-- statement:
--   Definitions and structural lemmas for Arch Sz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
namespace GlobalTheory.ConjSize
variable {K : Type} [Field K] (ι τ : K →+* ℂ)
def Sz (z : ℂ) (B : ℝ) : Prop := ∃ y, ι y = z ∧ ‖τ y‖ ≤ B
def Un (z : ℂ) : Prop := ∃ y, ι y = z ∧ ‖τ y‖ = 1
variable {ι τ}
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Local
end GlobalTheory.ConjSize
end


