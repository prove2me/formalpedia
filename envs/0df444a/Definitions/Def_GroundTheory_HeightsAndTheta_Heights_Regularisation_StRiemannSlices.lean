-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:57.439818+00:00
-- url     : https://prove2.me/theorems/730d4b06-1abe-420c-848a-74a772d66835
-- title:
--   St Riemann Slices
-- statement:
--   Definitions and structural lemmas for St Riemann Slices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/StRiemannSlices.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology
noncomputable section
def RiemannExtensionSlices.Statement : Prop :=
  ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ),
    DifferentiableOn ℂ G (ball (0 : Fin n → ℂ) 1 ∩ {z | ∀ i, z i ≠ 0}) →
    (∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ i : Fin n, (∀ j, j ≠ i → z j ≠ 0) →
      ∃ c : ℂ, Tendsto (fun x : ℂ => G (Function.update z i x)) (𝓝[≠] 0) (𝓝 c)) →
    ∃ G' : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ G' (ball (0 : Fin n → ℂ) 1) ∧
      ∀ z ∈ ball (0 : Fin n → ℂ) 1, (∀ i, z i ≠ 0) → G' z = G z
end
end GroundTheory.Heights₂.Heights.Regular


