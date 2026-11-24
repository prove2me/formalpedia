-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatReindexRows
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatReindexRows
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:09.153294+00:00
-- url     : https://prove2.me/theorems/4e4a384f-ffcc-45ba-909d-35eb87009531
-- title:
--   Schwartz Bruhat Reindex Rows
-- statement:
--   Definitions and structural lemmas for Schwartz Bruhat Reindex Rows, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatReindexRows.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
def rowRenum (e : A ≃ A') : Matrix A D k ≃ₜ Matrix A' D k where
  toFun Y := Y.submatrix e.symm id
  invFun Y' := Y'.submatrix e id
  left_inv Y := by ext i j; simp
  right_inv Y' := by ext i j; simp
  continuous_toFun := continuous_id.matrix_submatrix _ _
  continuous_invFun := continuous_id.matrix_submatrix _ _
def glRenum (e : A ≃ A') : GL A' k →* GL A k :=
  Units.map (Matrix.reindexAlgEquiv k k e.symm).toMonoidHom
end GlobalTheory.RankStrata


