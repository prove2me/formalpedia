-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveDiscriminant
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveDiscriminant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:41.005995+00:00
-- url     : https://prove2.me/theorems/6fa418f1-8d08-484b-8671-4783a87de03c
-- title:
--   St Primitive Discriminant
-- statement:
--   Definitions and structural lemmas for St Primitive Discriminant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimitiveDiscriminant.lean

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
variable {n d : ℕ}
abbrev projAlgebra (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
  (projHom J A).toRingHom.toAlgebra
def sum₂ (c : Fin n → ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (c j) * X j
def formMinpoly (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (c : Fin n → ℂ) :
    Polynomial (MvPolynomial (Fin d) ℂ) :=
  letI := projAlgebra J A
  minpoly (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J (sum₂ c))
def PrimitiveDiscriminant.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∃ D : MvPolynomial (Fin n) ℂ, D ≠ 0 ∧ ∀ c : Fin n → ℂ, eval c D ≠ 0 →
        (formMinpoly J A c).Monic ∧ (formMinpoly J A c).natDegree = projDegree J A ∧
        Polynomial.eval₂ (pullback A).toRingHom (sum₂ c) (formMinpoly J A c) ∈ J ∧
        (formMinpoly J A c).discr ≠ 0 ∧
        ∀ j : Fin n, ∃ G : Polynomial (MvPolynomial (Fin d) ℂ),
          pullback A (formMinpoly J A c).discr * X j -
            Polynomial.eval₂ (pullback A).toRingHom (sum₂ c) G ∈ J
end
end GroundTheory.Heights₂.Heights.ComplexSets


