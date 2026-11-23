-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
-- name    : Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:04.974778+00:00
-- url     : https://prove2.me/theorems/6f564008-727e-4387-88a3-6b89dc2c9492
-- title:
--   Exists Gl Isometry Comp Eq Of Nondegenerate
-- statement:
--   Definitions and structural lemmas for Exists Gl Isometry Comp Eq Of Nondegenerate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
section Abstract
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
def quasiRefl (B : V →ₗ[E] V →ₛₗ[c] E) (v : V) (a : E) : V →ₗ[E] V :=
  LinearMap.id - (a⁻¹ • B.flip v).smulRight v
end Abstract
section MatrixForm
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n] [DecidableEq n]
end MatrixForm
section CM
open NumberField ReciprocityTheory.ChartRestriction.G
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end CM
end GlobalTheory.HermWitt


