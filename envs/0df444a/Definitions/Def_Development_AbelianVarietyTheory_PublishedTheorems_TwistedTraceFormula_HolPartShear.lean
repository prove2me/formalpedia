-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HolPartShear
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HolPartShear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:09.468411+00:00
-- url     : https://prove2.me/theorems/63440e0a-6785-42ef-a263-886504bd7dfd
-- title:
--   Hol Part Shear
-- statement:
--   Definitions and structural lemmas for Hol Part Shear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HolPartShear.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
namespace GlobalTheory.Published.Metaplectic.Model
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def chirp (C : Matrix ι ι ℝ) (f : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => cexp (-π * I * ((x ⬝ᵥ C *ᵥ x : ℝ) : ℂ)) * f x
def sgnRep (E : Type) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [ContinuousConstSMul ℂ E] :
    ℤˣ →* (E →L[ℂ] E) where
  toFun g := (((g : ℤ) : ℂ)) • (1 : E →L[ℂ] E)
  map_one' := by simp
  map_mul' g h := by ext; simp [smul_smul, mul_comm]
end GlobalTheory.Published.Metaplectic.Model
end


