-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StImplicitCurve
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StImplicitCurve
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:55.654892+00:00
-- url     : https://prove2.me/theorems/a153daee-4ee7-4ceb-a8ca-aa175c358ce9
-- title:
--   St Implicit Curve
-- statement:
--   Definitions and structural lemmas for St Implicit Curve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StImplicitCurve.lean

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
namespace GroundTheory.Heights₂.Heights
open Matrix Topology
noncomputable section
def ImplicitCurve.Statement : Prop :=
  ∀ (n k : ℕ) (γ : (Fin (k + 1) → ℂ) → Fin n → ℂ) (R : ℝ) (L : Matrix (Fin k) (Fin n) ℂ)
    (s : Fin (k + 1) → ℂ),
    DifferentiableOn ℂ γ (Metric.ball 0 R) → s ∈ Metric.ball 0 R →
    Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ t)) s) →
      ∃ r > 0, ∃ φ : (Fin 1 → ℂ) → Fin (k + 1) → ℂ,
        DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ φ 0 = s ∧
        (∀ τ ∈ Metric.ball 0 r,
          φ τ ∈ Metric.ball 0 R ∧ φ τ 0 = s 0 + τ 0 ∧ L *ᵥ γ (φ τ) = L *ᵥ γ s) ∧
        ∃ P ∈ 𝓝 s, ∀ t ∈ P, L *ᵥ γ t = L *ᵥ γ s → ∃ τ ∈ Metric.ball 0 r, φ τ = t
end
end GroundTheory.Heights₂.Heights


