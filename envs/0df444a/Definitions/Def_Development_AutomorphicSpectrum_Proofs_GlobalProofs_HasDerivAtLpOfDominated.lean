-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HasDerivAtLpOfDominated
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_HasDerivAtLpOfDominated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:58.837188+00:00
-- url     : https://prove2.me/theorems/c53fda69-1af8-47c5-b1d6-b659e8b6b26c
-- title:
--   Has Deriv At Lp Of Dominated
-- statement:
--   Definitions and structural lemmas for Has Deriv At Lp Of Dominated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/HasDerivAtLpOfDominated.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HolPartShear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RealMpData
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.CompanionTheory.Hypotheses₂ Filter Topology
open scoped Real SchwartzMap ComplexConjugate
namespace GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve
variable {l : Type} [Fintype l]
def qf (Z : Matrix l l ℂ) (x : EuclideanSpace ℝ l) : ℂ :=
  ∑ j, ∑ k, Z j k * (x j : ℂ) * (x k : ℂ)
end GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve
end


