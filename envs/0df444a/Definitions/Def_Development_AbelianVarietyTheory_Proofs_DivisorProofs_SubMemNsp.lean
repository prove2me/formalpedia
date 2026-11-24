-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:16.29287+00:00
-- url     : https://prove2.me/theorems/c4d6f258-8b3e-4953-8317-703ad79f7bed
-- title:
--   Sub Mem Nsp
-- statement:
--   Definitions and structural lemmas for Sub Mem Nsp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubMemNsp.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
namespace GlobalTheory.RankStrata
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def Nsp (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) :
    Submodule ℂ (Matrix A D k → ℂ) :=
  Submodule.span ℂ {Z | ∃ g : GL A k, ∃ Ψ' ∈ SB (Matrix A D k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'}
variable {k}
end GlobalTheory.RankStrata


