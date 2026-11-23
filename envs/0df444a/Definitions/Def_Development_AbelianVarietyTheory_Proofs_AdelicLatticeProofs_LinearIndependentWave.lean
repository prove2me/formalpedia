-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:46.326744+00:00
-- url     : https://prove2.me/theorems/57b62ff4-f384-4c12-8a14-664ef15eb8f9
-- title:
--   Linear Independent Wave
-- statement:
--   Definitions and structural lemmas for Linear Independent Wave, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/LinearIndependentWave.lean

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
namespace GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
open Classical in

def ind (L : AddSubgroup G) (t : G) : ℂ := if t ∈ L then 1 else 0
def wave (χ : G → G → ℂ) (L : AddSubgroup G) (x y : G) : G → ℂ := fun t => χ (t + x) y * ind L (t + x)
def waveSpan (χ : G → G → ℂ) (X Y L : AddSubgroup G) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {Φ | ∃ x ∈ X, ∃ y ∈ Y, Φ = wave χ L x y}
structure IsBichar (χ : G → G → ℂ) : Prop where
  left : ∀ a b y, χ (a + b) y = χ a y * χ b y
  right : ∀ a y z, χ a (y + z) = χ a y * χ a z
  zero_left : ∀ y, χ 0 y = 1
  zero_right : ∀ a, χ a 0 = 1
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
end GlobalTheory.PlaceModel
end


