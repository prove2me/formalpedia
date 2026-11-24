-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFunctionFieldDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFunctionFieldDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:30.256818+00:00
-- url     : https://prove2.me/theorems/5f30be6b-afac-41c7-976f-5fb28ef479ce
-- title:
--   St Function Field Degree
-- statement:
--   Definitions and structural lemmas for St Function Field Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFunctionFieldDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveDiscriminant
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
def FunctionFieldDegree.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    IsFiniteProjection J A →
    letI := projAlgebra J A
    ∀ (K L : Type) [Field K] [Field L] [Algebra (MvPolynomial (Fin d) ℂ) K]
      [IsFractionRing (MvPolynomial (Fin d) ℂ) K] [Algebra (MvPolynomial (Fin n) ℂ ⧸ J) L]
      [IsFractionRing (MvPolynomial (Fin n) ℂ ⧸ J) L] [Algebra (MvPolynomial (Fin d) ℂ) L]
      [Algebra K L] [IsScalarTower (MvPolynomial (Fin d) ℂ) K L]
      [IsScalarTower (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) L],
      FiniteDimensional K L ∧ Module.finrank K L = projDegree J A ∧
        IntermediateField.adjoin K
          (Set.range fun j => algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) L (Ideal.Quotient.mk J (X j))) = ⊤
end
end GroundTheory.Heights₂.Heights.ComplexSets


