-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatrices
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatrices
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:29.927104+00:00
-- url     : https://prove2.me/theorems/4d3f7133-c9e5-55e8-947c-8e4ea913f4a5
-- title:
--   Measure Uniformizer Multiple Matrices
-- statement:
--   Definitions and structural lemmas for Measure Uniformizer Multiple Matrices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureUniformizerMultipleMatrices.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslateStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
namespace GlobalTheory.CompanionTheory.QL.Vol
noncomputable def scalarInvGL {F : Type} [Field F] (m : ℕ) (x : F) (hx : x ≠ 0) : GL (Fin m) F :=
  Units.map (Matrix.scalar (Fin m) : F →+* Matrix (Fin m) (Fin m) F).toMonoidHom (Units.mk0 x⁻¹ (inv_ne_zero hx))
end GlobalTheory.CompanionTheory.QL.Vol


