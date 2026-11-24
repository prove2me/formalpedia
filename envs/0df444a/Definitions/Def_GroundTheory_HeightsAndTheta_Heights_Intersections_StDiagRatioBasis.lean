-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StDiagRatioBasis
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StDiagRatioBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:09.845513+00:00
-- url     : https://prove2.me/theorems/e94213c0-0f21-4e5a-8ad2-23d05b56c7d6
-- title:
--   St Diag Ratio Basis
-- statement:
--   Definitions and structural lemmas for St Diag Ratio Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StDiagRatioBasis.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StYYRatioBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
def DiagRatioBasis.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type)
    [AddCommGroup E] [Module Ω E] (Φ : Type) [Field Φ] [CharZero Φ] [Algebra Ω Φ] (x : ι → Ω)
    (e b : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω) (g : κ → Fin 2 → Ω) (i₀ : ι) (l₀ : ν)
    (k₀ k₁ : κ) (d : ℕ) (t : Fin d → Ω) (a : Φ),
    x i₀ ≠ 0 → AlgebraicIndependent ℚ t →
    (∀ n, t n ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)) →
    (∀ j, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) (x j / x i₀)) →
    δ l₀ ≠ 0 → (∀ l, δ l / δ l₀ ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)) →
    (∀ k q, φ k (b q) = x i₀ * g k q) →
    (∀ k q, g k q ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)) →
    g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0 → Transcendental Ω a →
      ∃ (c : ∀ k, T.wwIdx ι ν κ k) (t' : Fin (d + 1) → Φ), (∀ k, T.wwCoord x δ e φ a a ⟨k, c k⟩ ≠ 0) ∧
        AlgebraicIndependent ℚ t' ∧
        (∀ n, t' n ∈ IntermediateField.adjoin ℚ (coneRatios (T.wwCoord x δ e φ a a) c)) ∧
        ∀ r ∈ coneRatios (T.wwCoord x δ e φ a a) c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t')) r
end
end GroundTheory.Heights₂.Heights.Inter


