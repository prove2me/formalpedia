-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:35.786492+00:00
-- url     : https://prove2.me/theorems/48f766a5-c61b-4ccb-aa29-cf4c779ac8bf
-- title:
--   Gauss Zero
-- statement:
--   Definitions and structural lemmas for Gauss Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
def hmon (n : ℤ) (z : ℂ) : ℂ := if 0 ≤ n then (starRingEnd ℂ z) ^ n.toNat else z ^ (-n).toNat
def gauss (n : I → ℤ) (w : I → ℂ) : ℂ :=
  ∏ i, hmon (n i) (w i) * Complex.exp ((-2 * Real.pi * ‖w i‖ ^ 2 : ℝ) : ℂ)
def dil (y : I → ℝ) (v : I → ℂ) : I → ℂ := fun i => (Real.exp (y i / 2) : ℂ) * v i
def theta {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ) (y : I → ℝ) : ℂ :=
  ∑' j, a j * gauss n (dil y (e j))
def emb {K : Type} [Field K] (φ : I → K →+* ℂ) (α : K) : I → ℂ := fun i => φ i α
def ulog {K : Type} [Field K] [NumberField K] (φ : I → K →+* ℂ) (u : (𝓞 K)ˣ) : I → ℝ :=
  fun i => Real.log (‖φ i ((u : 𝓞 K) : K)‖ ^ 2)
end GlobalTheory.HeckeTheta


