-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_CobOn
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_CobOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:01.427412+00:00
-- url     : https://prove2.me/theorems/0043775d-5c61-4d60-a9f0-eb2ed132fc09
-- title:
--   Cob On
-- statement:
--   Definitions and structural lemmas for Cob On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/CobOn.lean

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
namespace GlobalTheory.KEdge
variable {Γ : Type*} [Group Γ] {N : ℕ}
def edge (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ h : Γ) : ZMod N :=
  η (σ * h * σ⁻¹) - η h - (x h).toAdd * (y σ).toAdd + (x σ).toAdd * (y h).toAdd
def CobOn (Δ : Subgroup Γ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) : Prop :=
  ∀ g ∈ Δ, ∀ h ∈ Δ, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g
end GlobalTheory.KEdge


