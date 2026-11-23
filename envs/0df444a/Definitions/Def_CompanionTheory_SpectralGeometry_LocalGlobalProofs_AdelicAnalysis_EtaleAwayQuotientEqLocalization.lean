-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EtaleAwayQuotientEqLocalization
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EtaleAwayQuotientEqLocalization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:08.713976+00:00
-- url     : https://prove2.me/theorems/7662ccf2-df4b-4a5a-98de-f0264254c0b7
-- title:
--   Etale Away Quotient Eq Localization
-- statement:
--   Definitions and structural lemmas for Etale Away Quotient Eq Localization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EtaleAwayQuotientEqLocalization.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.TraceFormGram
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
def trGram (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) F :=
  fun p q => Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)
section CM
variable [NumberField F] [NumberField E]
end CM
end GlobalTheory.CompanionTheory.SW.TraceFormGram
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW
end GlobalTheory.CompanionTheory.SW


