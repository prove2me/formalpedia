-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
-- name    : Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:09.909421+00:00
-- url     : https://prove2.me/theorems/27bf6e2d-5bf3-40ad-ad35-b11cba2af186
-- title:
--   Pos Index Map Eq Card Of Congr Diagonal
-- statement:
--   Definitions and structural lemmas for Pos Index Map Eq Card Of Congr Diagonal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
section Complex
variable {n m : Type*} [Fintype n] [Fintype m]
def posDims (G : Matrix n n ℂ) : Set ℕ :=
  {d | ∃ W : Submodule ℂ (n → ℂ), finrank ℂ W = d ∧
    ∀ x ∈ W, x ≠ 0 → 0 < (x ⬝ᵥ G *ᵥ star x).re}
noncomputable def posIndex (G : Matrix n n ℂ) : ℕ := sSup (posDims G)
noncomputable def negIndex (G : Matrix n n ℂ) : ℕ := posIndex (-G)
variable [DecidableEq n]
end Complex
section NormalForm
variable {r s : ℕ}
end NormalForm
section CM
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {n : Type*} [Fintype n] [DecidableEq n]
end CM
end GlobalTheory.Inertia


