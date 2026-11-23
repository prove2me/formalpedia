-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InverseUnipotentVolumeConjDiagonalUnitsGLMul
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_InverseUnipotentVolumeConjDiagonalUnitsGLMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:46.429151+00:00
-- url     : https://prove2.me/theorems/6c701351-b6a2-4fd1-8a49-5a7572de531a
-- title:
--   Inverse Unipotent Volume Conj Diagonal Units GLMul
-- statement:
--   Definitions and structural lemmas for Inverse Unipotent Volume Conj Diagonal Units GLMul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
noncomputable section
namespace GlobalTheory.FunObj
open Matrix
section Ratio
variable {G : Type*} [Group G]
def idxRatio (A B : Subgroup G) : ℚ := (B.relIndex A : ℚ) / A.relIndex B
variable [TopologicalSpace G] [IsTopologicalGroup G]
end Ratio
section Diag
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
end Diag
end GlobalTheory.FunObj
namespace GlobalTheory.FunObj
open Matrix
section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
end Main
end GlobalTheory.FunObj


