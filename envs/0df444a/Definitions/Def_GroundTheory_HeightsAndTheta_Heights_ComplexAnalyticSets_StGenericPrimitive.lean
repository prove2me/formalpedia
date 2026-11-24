-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:11.802098+00:00
-- url     : https://prove2.me/theorems/2a8933d8-91b3-475e-9f10-c1408e05dfb9
-- title:
--   St Generic Primitive
-- statement:
--   Definitions and structural lemmas for St Generic Primitive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGenericPrimitive.lean

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
namespace GroundTheory.Heights₂.Heights.ComplexSets
noncomputable section
def GenericPrimitive.Statement : Prop :=
  ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (n : ℕ) (x : Fin n → L),
    IntermediateField.adjoin K (Set.range x) = ⊤ →
      ∃ D : MvPolynomial (Fin n) k, D ≠ 0 ∧ ∀ c : Fin n → k, MvPolynomial.eval c D ≠ 0 →
        IntermediateField.adjoin K {∑ j, c j • x j} = ⊤
end
end GroundTheory.Heights₂.Heights.ComplexSets


