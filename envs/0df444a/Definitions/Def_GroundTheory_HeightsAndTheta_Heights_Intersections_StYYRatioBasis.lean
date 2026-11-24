-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StYYRatioBasis
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StYYRatioBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:57.260615+00:00
-- url     : https://prove2.me/theorems/c5ba9cc5-e2a8-41dd-8281-18f816b2e421
-- title:
--   St YYRatio Basis
-- statement:
--   Definitions and structural lemmas for St YYRatio Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StYYRatioBasis.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreProduct
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
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
def YYRatioBasis.Statement : Prop :=
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
      ∃ (c : ∀ k, T.yyIdx ι ν κ k) (t' : Fin (d + 1) → Φ), (∀ k, T.yyCoord x δ e φ a ⟨k, c k⟩ ≠ 0) ∧
        AlgebraicIndependent ℚ t' ∧
        (∀ n, t' n ∈ IntermediateField.adjoin ℚ (coneRatios (T.yyCoord x δ e φ a) c)) ∧
        ∀ r ∈ coneRatios (T.yyCoord x δ e φ a) c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t')) r
def exRatioG : Unit ⊕ Unit → Fin 2 → ℚ := fun k q => exφ k (Pi.basisFun ℚ (Fin 2) q)
end
end GroundTheory.Heights₂.Heights.Inter


