-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatrices
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatrices
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:00.398213+00:00
-- url     : https://prove2.me/theorems/8034e5bd-7d0b-5668-b957-66adaf969264
-- title:
--   Measure Invertible Integral Matrices
-- statement:
--   Definitions and structural lemmas for Measure Invertible Integral Matrices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureInvertibleIntegralMatrices.lean

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatricesStatement
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
noncomputable section
namespace GlobalTheory.CompanionTheory.QL.VolK
section
variable {F : Type} [Field F] [ValuativeRel F]
def red (x : F) : 𝓀[F] :=
  open Classical in if h : x ∈ 𝒪[F] then IsLocalRing.residue 𝒪[F] ⟨x, h⟩ else 0
def redM {r : ℕ} (x : Matrix (Fin r) (Fin r) F) : Matrix (Fin r) (Fin r) 𝓀[F] := x.map red
def toO {r : ℕ} {x : Matrix (Fin r) (Fin r) F} (h : x ∈ intMat 𝒪[F] r r) :
    Matrix (Fin r) (Fin r) 𝒪[F] := fun i j => ⟨x i j, h i j⟩
end
end GlobalTheory.CompanionTheory.QL.VolK


