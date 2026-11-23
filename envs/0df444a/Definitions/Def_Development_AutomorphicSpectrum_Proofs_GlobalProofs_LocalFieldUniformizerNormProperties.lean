-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:24.58195+00:00
-- url     : https://prove2.me/theorems/ce745ad4-5573-44e6-affb-75987f400d83
-- title:
--   Local Field Uniformizer Norm Properties
-- statement:
--   Definitions and structural lemmas for Local Field Uniformizer Norm Properties, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldUniformizerNormProperties.lean

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
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
namespace GlobalTheory.CompanionTheory.QL.NormalisedValue
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
theorem val_pi_lt_one (h : LF O ϖ nrm q) : ValuativeRel.valuation F ϖ < 1 := by
  exact (h.lt_one ϖ).2 ⟨1, O.one_mem, (mul_one ϖ).symm⟩
end GlobalTheory.CompanionTheory.QL.NormalisedValue


