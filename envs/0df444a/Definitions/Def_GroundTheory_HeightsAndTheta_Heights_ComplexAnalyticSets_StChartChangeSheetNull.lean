-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeSheetNull
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeSheetNull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:17.089897+00:00
-- url     : https://prove2.me/theorems/4d33bfdd-746b-406c-ae58-705cd9899f70
-- title:
--   St Chart Change Sheet Null
-- statement:
--   Definitions and structural lemmas for St Chart Change Sheet Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StChartChangeSheetNull.lean

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
noncomputable section
def ChartChangeSheetNull.Statement : Prop :=
  ∀ (n d : ℕ) (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (u u' : Fin n → ℂ) (U U' : Set (Fin n → ℂ)) (Φ Ψ : (Fin n → ℂ) → Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    J'.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') = d →
    linForm u ∉ J → linForm u' ∉ J' → IsFiniteProjection J A → IsFiniteProjection J' A' →
    IsOpen U → IsOpen U' → zeroSet J \ {x | linEval u x = 0} ⊆ U →
    zeroSet J' \ {x | linEval u' x = 0} ⊆ U' →
    DifferentiableOn ℂ Φ U' → DifferentiableOn ℂ Ψ U →
    Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}) →
    Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}) →
    (∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x) →
    (∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x) →
      volume ((fun x => A *ᵥ x) ''
        {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧
          ¬ (linEval u x ≠ 0 ∧ ∃ s', IsSheetAt J' A' (Ψ x) s')}) = 0
namespace ChartChange
def inv1 (x : Fin 1 → ℂ) : Fin 1 → ℂ := fun _ => (x 0)⁻¹
end ChartChange
end
end GroundTheory.Heights₂.Heights


