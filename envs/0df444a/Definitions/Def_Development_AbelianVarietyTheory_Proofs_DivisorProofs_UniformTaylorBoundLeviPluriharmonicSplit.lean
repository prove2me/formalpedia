-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplit
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:12.103034+00:00
-- url     : https://prove2.me/theorems/ee2555d0-b312-4b10-a34d-270ec17730f4
-- title:
--   Uniform Taylor Bound Levi Pluriharmonic Split
-- statement:
--   Definitions and structural lemmas for Uniform Taylor Bound Levi Pluriharmonic Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
namespace GlobalTheory.PluriTaylor
open Complex Set
variable {n : ℕ}
noncomputable section
def lc (F : V n →L[ℝ] ℝ) (j : Fin n) : ℂ :=
  ((F (bas n j) : ℂ) - I * (F (I • bas n j) : ℂ)) / 2
def qc (B : V n →L[ℝ] V n →L[ℝ] ℝ) (j k : Fin n) : ℂ :=
  ((B (bas n j) (bas n k) : ℂ) - (B (I • bas n j) (I • bas n k) : ℂ) -
    I * ((B (bas n j) (I • bas n k) : ℂ) + (B (I • bas n j) (bas n k) : ℂ))) / 8
end
end GlobalTheory.PluriTaylor
namespace GlobalTheory.PluriTaylor
open Set
variable {n : ℕ}
end GlobalTheory.PluriTaylor
namespace GlobalTheory.PluriTaylor
open Complex
end GlobalTheory.PluriTaylor


