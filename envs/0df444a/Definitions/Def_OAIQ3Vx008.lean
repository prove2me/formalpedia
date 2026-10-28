-- Prove2me | Definitions.Def_OAIQ3Vx008
-- name    : OAIQ3Vx008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:33:48.411796+00:00
-- url     : https://prove2.me/theorems/315398fa-e861-4ad9-b846-0bf9c73afc88
-- title:
--   Definitions bundle OAIQ3Vx008 of the split of OpenAI, Strongly rational unitary vertex operator algebras and conformal nets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinimalVertex.main`, carved from OpenAI's openai/math development (OpenAI, *Strongly rational unitary vertex operator algebras and conformal nets*, OpenAI Math Release, September 25, 2026, result family 280, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 inductive type or structure. The definitions and types are `OAI.StronglyRationalVOA.IrreducibleConformalNetStructure`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/VertexAlgebra, in whole or in part: [`VertexAlgebra_NetAxioms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/VertexAlgebra/VertexAlgebra/NetAxioms.lean).
--
--   **Imports.** It imports the published bundle `Def_VertexAlgebraNet`; the bundles `OAIQ3Vx003` and `OAIQ3Vx005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ3Vx012`.
-- source:
--   OpenAI, Strongly rational unitary vertex operator algebras and conformal nets, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 280; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/VertexAlgebra at commit adc7f12

import Mathlib
import Definitions.Def_VertexAlgebraNet
import Definitions.Def_OAIQ3Vx003
import Definitions.Def_OAIQ3Vx005

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_NetAxioms
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Topology MatrixGroups
namespace StronglyRationalVOA



structure IrreducibleConformalNetStructure {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : ProperCircleArc → VonNeumannAlgebra H) where
  separable : TopologicalSpace.SeparableSpace H
  carrier_congr : ∀ I J, I.carrier=J.carrier → N I=N J
  isotony : ∀ I J, I.carrier ⊆ J.carrier → N I ≤ N J
  locality : ∀ I J, Disjoint I.carrier J.carrier → N I ≤ (N J).commutant
  mobius : PSL(2,ℝ) →* (H ≃ₗᵢ[ℂ] H)
  mobius_continuous : Continuous mobius
  diffeomorphism : SmoothCircleDiffeomorphism →* ProjectiveUnitaryGroup H
  diffeomorphism_continuous : Continuous diffeomorphism
  extends_mobius : ∀ F, diffeomorphism (CircleMobiusGeometry.inclusion (CircleMobiusGeometry.projectiveStandardAction F))=QuotientGroup.mk (mobius F)
  covariance : ∀ F I J, J.carrier=SmoothCircleDiffeomorphism.action F '' I.carrier →
    ∀ B : H →L[ℂ] H, projectiveConjugation (diffeomorphism F) B ∈ N J ↔ B ∈ N I
  local_action : ∀ F I, (∀ x ∈ I.carrier, SmoothCircleDiffeomorphism.action F x=x) →
    ∀ B ∈ N I, projectiveConjugation (diffeomorphism F) B=B
  vacuum : H
  vacuum_norm : ‖vacuum‖=1
  vacuum_invariant : ∀ F, mobius F vacuum=vacuum
  vacuum_unique : ∀ x : H, (∀ F, mobius F x=x) → ∃ c : ℂ, x=c • vacuum
  vacuum_cyclic : globalCyclicSpace N vacuum=⊤
  hamiltonian : H →ₗ.[ℂ] H
  hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian
  positive_energy : ∀ x y, (x,y) ∈ hamiltonian.graph → 0 ≤ (inner ℂ x y).re
  rotation_flow : ∀ t : ℝ,
    (mobius (QuotientGroup.mk (CircleMobiusGeometry.rotationMatrix t))).toLinearIsometry.toContinuousLinearMap=
      SymmetricOperator.flow hamiltonian hamiltonian_selfAdjoint t
  irreducible : ∀ Q : H →L[ℂ] H, (∀ I, Q ∈ (N I).commutant) →
    ∃ c : ℂ, Q=c • (1 : H →L[ℂ] H)
end StronglyRationalVOA

end

end OAI
end


