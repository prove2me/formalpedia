-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLFewZerosSmallDisc
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLFewZerosSmallDisc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:45.326719+00:00
-- url     : https://prove2.me/theorems/40e22e69-24a8-4a2c-adc8-b1e1e05fe6ce
-- title:
--   Dirichlet LFew Zeros Small Disc
-- statement:
--   Definitions and structural lemmas for Dirichlet LFew Zeros Small Disc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DirichletLFewZerosSmallDisc.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
namespace GlobalTheory.SmallDiscZeros
end GlobalTheory.SmallDiscZeros


