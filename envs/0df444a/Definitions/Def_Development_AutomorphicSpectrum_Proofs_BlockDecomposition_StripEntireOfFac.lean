-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:53.244877+00:00
-- url     : https://prove2.me/theorems/febfb4e6-de37-4181-88b9-ed38cdba7e93
-- title:
--   Strip Entire Of Fac
-- statement:
--   Definitions and structural lemmas for Strip Entire Of Fac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEisGal
section Slice
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
end Slice
section Conds
variable {G : Type} [Group G]
variable {Γ A B : Subgroup G} {a b h : G → ℝ} {N R Rw : ℝ}
end Conds
section Series
variable {G : Type} [Group G]
variable {L W : Type} [NormedAddCommGroup L] [NormedSpace ℂ L] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [CompleteSpace W]
end Series
section Eis
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
  [NormedSpace ℂ W]
end Eis
end GlobalTheory.CompanionTheory.RgEisGal


