-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydisc
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydisc
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:42.15964+00:00
-- url     : https://prove2.me/theorems/c5d6f40c-0669-412c-b2fb-64d8570a4fc3
-- title:
--   Period Chart Uniform Constants Half Polydisc
-- statement:
--   Definitions and structural lemmas for Period Chart Uniform Constants Half Polydisc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodChartUniformConstantsHalfPolydisc.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
namespace GlobalTheory.UnifConsts
end GlobalTheory.UnifConsts
namespace GlobalTheory.UnifConsts
noncomputable def blockEquiv (g rk : ℕ) :
    Fin (Fintype.card {j : Fin g // j.val < rk}) ⊕ Fin (Fintype.card {j : Fin g // ¬ j.val < rk})
      ≃ Fin g :=
  (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans (Equiv.sumCompl _)
end GlobalTheory.UnifConsts
namespace GlobalTheory.UnifConsts
end GlobalTheory.UnifConsts


