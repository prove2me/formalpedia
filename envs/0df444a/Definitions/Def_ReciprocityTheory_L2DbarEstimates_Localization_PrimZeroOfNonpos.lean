-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_PrimZeroOfNonpos
-- name    : ReciprocityTheory_L2DbarEstimates_Localization_PrimZeroOfNonpos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:59.977199+00:00
-- url     : https://prove2.me/theorems/a1c6d9a3-8a36-42b0-be28-5def544f0518
-- title:
--   Prim Zero Of Nonpos
-- statement:
--   Definitions and structural lemmas for Prim Zero Of Nonpos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/PrimZeroOfNonpos.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace EulerCharacteristicLength
def prim (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in (0:ℝ)..t, f x
def P : ℝ → ℝ := prim expNegInvGlue
def sig : ℝ → ℝ := prim P
def Fs (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range m, c k * sig (t - (a + k))
def Fs1 (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range m, c k * P (t - (a + k))
def Fs2 (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, c k * expNegInvGlue (t - (a + k))
def chiF (c : ℕ → ℝ) (a : ℝ) (t : ℝ) : ℝ := ∑' k : ℕ, c k * sig (t - (a + k))
end EulerCharacteristicLength
end
end ReciprocityTheory.L2DbarEstimates.F


