-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:56.372241+00:00
-- url     : https://prove2.me/theorems/7452698d-4b3d-405d-8a34-19eb35f8a90f
-- title:
--   Exists Schwartz Bruhat Convolution Local Field Power
-- statement:
--   Definitions and structural lemmas for Exists Schwartz Bruhat Convolution Local Field Power, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSchwartzBruhatConvolutionLocalFieldPower.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsWeakIntegralOfIsLocallyConstantOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
namespace GlobalTheory.SBConv
section Abstract
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
def translate (Ψ : SB G) (y : G) : SB G :=
  ⟨fun x => Ψ.1 (x - y), Ψ.2.1.comp_continuous (continuous_sub_right y),
    Ψ.2.2.comp_homeomorph (Homeomorph.subRight y)⟩
end Abstract
end GlobalTheory.SBConv


