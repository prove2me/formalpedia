-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFactorThroughFlatMapFourierJacobiColumn
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFactorThroughFlatMapFourierJacobiColumn
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:16.999983+00:00
-- url     : https://prove2.me/theorems/8af55d60-d974-4398-82bc-17d139d75941
-- title:
--   Exists Factor Through Flat Map Fourier Jacobi Column
-- statement:
--   Definitions and structural lemmas for Exists Factor Through Flat Map Fourier Jacobi Column, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFactorThroughFlatMapFourierJacobiColumn.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
namespace GlobalTheory.LocFlat
section Lin
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
end Lin
end GlobalTheory.LocFlat


