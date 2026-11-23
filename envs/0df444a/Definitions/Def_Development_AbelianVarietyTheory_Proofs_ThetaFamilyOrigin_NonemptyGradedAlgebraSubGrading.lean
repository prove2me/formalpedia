-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:29.648811+00:00
-- url     : https://prove2.me/theorems/e38dc822-3121-4195-a945-5c5265549f42
-- title:
--   Nonempty Graded Algebra Sub Grading
-- statement:
--   Definitions and structural lemmas for Nonempty Graded Algebra Sub Grading, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.TorsionZero
open MvPolynomial
section Forms
variable {K σ : Type} [Field K]
end Forms
section Core
variable {K R : Type} [Field K] [CommRing R] [Algebra K R]
def subGrading (𝒜 : ℕ → Submodule K R) (N : ℕ) (T : Subalgebra K R) (e : ℕ) : Submodule K T :=
  (𝒜 (N * e)).comap T.val.toLinearMap
end Core
end GlobalTheory.TorsionZero


