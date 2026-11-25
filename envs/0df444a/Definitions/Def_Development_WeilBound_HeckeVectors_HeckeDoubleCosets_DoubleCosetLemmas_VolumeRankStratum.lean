-- Prove2me | Definitions.Def_Development_WeilBound_HeckeVectors_HeckeDoubleCosets_DoubleCosetLemmas_VolumeRankStratum
-- name    : Development_WeilBound_HeckeVectors_HeckeDoubleCosets_DoubleCosetLemmas_VolumeRankStratum
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:30.713239+00:00
-- url     : https://prove2.me/theorems/43276f00-7bce-5691-ba1c-7f6196e1ced7
-- title:
--   Volume Rank Stratum
-- statement:
--   Definitions and structural lemmas for Volume Rank Stratum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/VolumeRankStratum.lean

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslateStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_WeilIntegralUnipotentLeviFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace CompanionTheory.D.Upq.DoubleCosetLemmas.Kr
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ValuativeRel
variable {F : Type} [Field F]
def S0 (O : Subring F) (ϖ : F) (r d c : ℕ) : Set (Matrix (Fin (r + d)) (Fin (r + c)) F) :=
  {x | bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c}
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
end CompanionTheory.D.Upq.DoubleCosetLemmas.Kr
end


