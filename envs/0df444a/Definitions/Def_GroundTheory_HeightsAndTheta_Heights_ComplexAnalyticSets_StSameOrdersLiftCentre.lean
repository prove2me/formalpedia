-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrdersLiftCentre
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrdersLiftCentre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:01.878834+00:00
-- url     : https://prove2.me/theorems/914b9c4f-df67-48e9-8ae1-c1f63804a7f0
-- title:
--   St Same Orders Lift Centre
-- statement:
--   Definitions and structural lemmas for St Same Orders Lift Centre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSameOrdersLiftCentre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchOffHypersurface
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
open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
noncomputable section
def SameOrdersLiftCentre.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : NormalModel J)
    (γ γ' : VarBranch J 1 q) (Γ Γ' : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) →
    DifferentiableOn ℂ Γ (Metric.ball 0 γ.radius) →
    (∀ τ ∈ Metric.ball 0 γ.radius, Γ τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ τ) = γ.toFun τ) →
    DifferentiableOn ℂ Γ' (Metric.ball 0 γ'.radius) →
    (∀ τ ∈ Metric.ball 0 γ'.radius, Γ' τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ' τ) = γ'.toFun τ) →
    (∀ f : MvPolynomial (Fin n) ℂ, branchOrder γ f = branchOrder γ' f) →
      Γ 0 = Γ' 0
def lineDiagonalLift (τ : Fin 1 → ℂ) : Fin 1 ⊕ Fin 1 → ℂ := fun _ ↦ τ 0
end
end GroundTheory.Heights₂.Heights


