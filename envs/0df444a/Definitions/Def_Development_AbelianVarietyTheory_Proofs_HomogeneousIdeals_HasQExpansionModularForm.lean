-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:02.842805+00:00
-- url     : https://prove2.me/theorems/772188cd-5e2a-46b4-92b2-b26aa7aebea7
-- title:
--   Has QExpansion Modular Form
-- statement:
--   Definitions and structural lemmas for Has QExpansion Modular Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasQExpansionModularForm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real
noncomputable section
namespace GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
def HasQExpansion (h : ℝ) (f : ℍ → ℂ) (φ : PowerSeries ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun m ↦ coeff m φ * 𝕢 h τ ^ m) (f τ)
namespace HasQExpansion
variable {h : ℝ} {f g : ℍ → ℂ} {φ ψ : PowerSeries ℂ}
lemma qParam (h : ℝ) : HasQExpansion h (fun τ ↦ 𝕢 h τ) X := fun τ ↦ by
  have := hasSum_single (f := fun m ↦ coeff m (X : PowerSeries ℂ) * 𝕢 h τ ^ m) 1
    (fun m hm ↦ by simp [coeff_X, hm])
  simpa using this
end HasQExpansion
end GlobalTheory


