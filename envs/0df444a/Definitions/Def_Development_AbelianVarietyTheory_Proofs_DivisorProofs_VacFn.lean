-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VacFn
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_VacFn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:13.438416+00:00
-- url     : https://prove2.me/theorems/4f7855d0-b4a9-4450-8d38-ca972fa21773
-- title:
--   Vac Fn
-- statement:
--   Definitions and structural lemmas for Vac Fn, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VacFn.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace GlobalTheory.HeisLatVac
open Classical in

def vacFn {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K) : (κ → K) → ℂ :=
  fun x => if h : ∃ u ∈ Λ, x = x₀ + u.1 then
    χ h.choose * ψ₀ (-(x₀ ⬝ᵥ h.choose.2) - ⅟(2 : K) * (h.choose.1 ⬝ᵥ h.choose.2)) else 0
end GlobalTheory.HeisLatVac


