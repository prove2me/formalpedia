-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:43.442239+00:00
-- url     : https://prove2.me/theorems/ad6f2eaf-cc65-4ccf-b9b7-872acb2c6309
-- title:
--   Snd FDeriv Add Snd FDeriv IEq Zero Of Harmonic At Line
-- statement:
--   Definitions and structural lemmas for Snd FDeriv Add Snd FDeriv IEq Zero Of Harmonic At Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
namespace GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key
section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end General
variable {g : ℕ}
end GlobalTheory


