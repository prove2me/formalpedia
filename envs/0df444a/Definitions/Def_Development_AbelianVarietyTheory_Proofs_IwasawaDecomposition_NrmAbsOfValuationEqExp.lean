-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NrmAbsOfValuationEqExp
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NrmAbsOfValuationEqExp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:17.461659+00:00
-- url     : https://prove2.me/theorems/2c0f089b-fe03-4cb8-9fb8-53536677bc82
-- title:
--   Nrm Abs Of Valuation Eq Exp
-- statement:
--   Definitions and structural lemmas for Nrm Abs Of Valuation Eq Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NrmAbsOfValuationEqExp.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Mem.NrmCompl
open NumberField IsDedekindDomain
variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
def nrmAbs : AbsoluteValue (P.adicCompletion L) ℝ := NormedField.toAbsoluteValue (P.adicCompletion L)
end GlobalTheory.Mem.NrmCompl


