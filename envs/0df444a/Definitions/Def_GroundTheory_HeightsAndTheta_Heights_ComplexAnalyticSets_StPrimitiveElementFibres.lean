-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveElementFibres
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveElementFibres
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:23.60396+00:00
-- url     : https://prove2.me/theorems/070eae4f-1ded-4b6b-aba9-b74fa361ecb7
-- title:
--   St Primitive Element Fibres
-- statement:
--   Definitions and structural lemmas for St Primitive Element Fibres, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimitiveElementFibres.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
def PrimitiveElementFibres.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∃ (c : Fin n → ℂ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (Δ : MvPolynomial (Fin d) ℂ)
        (Q : Fin n → Polynomial (MvPolynomial (Fin d) ℂ)),
        m.Monic ∧ m.natDegree = projDegree J A ∧ Δ ≠ 0 ∧
          ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
            (m.map (eval y)).Separable ∧
            (∀ x ∈ fibre J A y, (m.map (eval y)).IsRoot (∑ j, c j * x j) ∧
              ∀ j, eval y Δ * x j = ((Q j).map (eval y)).eval (∑ j, c j * x j)) ∧
            ∀ τ : ℂ, (m.map (eval y)).IsRoot τ → ∃ x ∈ fibre J A y, ∑ j, c j * x j = τ
end
end GroundTheory.Heights₂.Heights.ComplexSets


