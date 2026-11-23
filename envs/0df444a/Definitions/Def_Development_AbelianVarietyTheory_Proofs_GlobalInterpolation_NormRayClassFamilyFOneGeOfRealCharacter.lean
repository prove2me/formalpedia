-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:33.0878+00:00
-- url     : https://prove2.me/theorems/0366e0b7-3382-4593-95f2-491c4230c82c
-- title:
--   Norm Ray Class Family FOne Ge Of Real Character
-- statement:
--   Definitions and structural lemmas for Norm Ray Class Family FOne Ge Of Real Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormRayClassFamilyFOneGeOfRealCharacter.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
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
namespace GlobalTheory.Hk.RealChar
def kerW (y w : ℝ) : ℝ := Real.exp (-(y / w)) * Real.exp (-w) / w
def besW (y : ℝ) : ℝ := ∫ w in Set.Ioi (0 : ℝ), kerW y w
def th (a : ℕ → ℝ) (t : ℝ) : ℝ := ∑' n : ℕ, a n * Real.exp (-(t * n))
def wt (w : ℝ) : ℝ := min w (1 / w) / (Real.sqrt w * w)
def bRe (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ℝ := ∑ g, (χ g).re * 𝓕.a g n
end GlobalTheory.Hk.RealChar
end


