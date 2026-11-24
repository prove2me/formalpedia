-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntChartChange
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntChartChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:27.206935+00:00
-- url     : https://prove2.me/theorems/4fac7a4a-e142-4825-99e2-7ae724456188
-- title:
--   St Var Int Chart Change
-- statement:
--   Definitions and structural lemmas for St Var Int Chart Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StVarIntChartChange.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ContDiff
noncomputable section
def VarIntChartChange.Statement : Prop :=
  ∀ (n d : ℕ) (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ) (U U' : Set (Fin n → ℂ))
    (Φ Ψ : (Fin n → ℂ) → Fin n → ℂ) (f f' : (Fin n → ℂ) → ℝ) (φ φ' : Fin d → (Fin n → ℂ) → ℝ)
    (c : Fin d → ℝ) (g : Fin d → (Fin n → ℂ) → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    J'.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') = d →
    linForm u ∉ J → linForm u' ∉ J' →
    IsOpen U → IsOpen U' → zeroSet J \ {x | linEval u x = 0} ⊆ U →
    zeroSet J' \ {x | linEval u' x = 0} ⊆ U' →
    DifferentiableOn ℂ Φ U' → DifferentiableOn ℂ Ψ U →
    Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}) →
    Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}) →
    (∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x) →
    (∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x) →
    Measurable f → Measurable f' → (∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, f' x = f (Φ x)) →
    (∀ k, SmoothNear (zeroSet J) (φ k)) → (∀ k, SmoothNear (zeroSet J') (φ' k)) →
    (∀ k, DifferentiableOn ℂ (g k) U') → (∀ k, ∀ x ∈ U', g k x ≠ 0) →
    (∀ k, ∀ x ∈ U', φ' k x = φ k (Φ x) + c k * Real.log ‖g k x‖) →
    (∀ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J A → Integrable (chartAbsDens J A f φ)) →
      varInt J d f φ = varInt J' d f' φ'
end
end GroundTheory.Heights₂.Heights


