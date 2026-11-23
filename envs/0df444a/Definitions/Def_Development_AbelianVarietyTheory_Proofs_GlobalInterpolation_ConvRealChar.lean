-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:49.416875+00:00
-- url     : https://prove2.me/theorems/e0028b0a-67a9-4be2-b819-b8ec9ccea0ef
-- title:
--   Conv Real Char
-- statement:
--   Definitions and structural lemmas for Conv Real Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
namespace GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
def normEq (K : Type) [Field K] [NumberField K] (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset
def dv (C : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  ((Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (Ideal.absNorm C)).toFinset).filter (· ∣ C)
def r (f : Ideal (𝓞 K) → ℝ) (C : Ideal (𝓞 K)) : ℝ := ∑ J ∈ dv C, f J
variable {M : ℕ} (D : RayData K M)
def chi (ε : D.G → ℝ) (I : Ideal (𝓞 K)) : ℝ :=
  if I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) then ε (D.cls I) else 0
end GlobalTheory.Hk.RaySq
end


