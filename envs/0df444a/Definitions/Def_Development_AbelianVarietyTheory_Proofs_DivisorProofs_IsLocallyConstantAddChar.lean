-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:00.827927+00:00
-- url     : https://prove2.me/theorems/82a88f55-1db4-477e-a5aa-dc6d72a81120
-- title:
--   Is Locally Constant Add Char
-- statement:
--   Definitions and structural lemmas for Is Locally Constant Add Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsLocallyConstantAddChar.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormPowTwoPowSubOneGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Pointwise
namespace GlobalTheory.WeilM
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
section Cov
variable {F} [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]
end Cov
end GlobalTheory.WeilM
end


