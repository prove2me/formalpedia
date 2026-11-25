-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_WeilIntegralUnipotentLeviFormula
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_WeilIntegralUnipotentLeviFormula
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:30:13.653501+00:00
-- url     : https://prove2.me/theorems/76bfc932-d837-4839-8d8e-f129b11fe9ce
-- title:
--   Weil Integral Unipotent Levi Formula
-- statement:
--   Definitions and structural lemmas for Weil Integral Unipotent Levi Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatricesStatement
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
namespace GlobalTheory.CompanionTheory.QL.PsiVolume
section Alg
variable {F : Type} [Field F]
abbrev psiSet (O : Subring F) (ϖ : F) {r d c : ℕ} (B : Matrix (Fin r) (Fin c) F) (m : GL (Fin c) F) :
    Set (Matrix (Fin (r + d)) (Fin (r + c)) F) :=
  {x | bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c ∧
    bAA x * B + bAD x * (m : Matrix (Fin c) (Fin c) F) ∈ intMat O r c ∧
    bDA x * B + bDD x * (m : Matrix (Fin c) (Fin c) F) ∈ intMat O d c}
end Alg
section Top
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
end Top
end GlobalTheory.CompanionTheory.QL.PsiVolume


