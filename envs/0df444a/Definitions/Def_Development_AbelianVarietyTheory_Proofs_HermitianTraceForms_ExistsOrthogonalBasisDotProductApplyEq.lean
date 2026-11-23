-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
-- name    : Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:43.566806+00:00
-- url     : https://prove2.me/theorems/8c1e919a-bcfa-4ccc-88ac-8b494c55430a
-- title:
--   Exists Orthogonal Basis Dot Product Apply Eq
-- statement:
--   Definitions and structural lemmas for Exists Orthogonal Basis Dot Product Apply Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.HermDiag
open Module Matrix
section Abstract
variable {E : Type*} [Field E] {c : E →+* E}
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  {n : Type*} [Fintype n]
end Abstract
section MatrixForm
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n]
variable [DecidableEq n]
end MatrixForm
section CM
open NumberField ReciprocityTheory.ChartRestriction.G
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end CM
end GlobalTheory.HermDiag


