-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyTangentGraphDense
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyTangentGraphDense
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:30.094119+00:00
-- url     : https://prove2.me/theorems/2d5aeed3-19bc-4865-9a33-512607c34a9b
-- title:
--   St Variety Tangent Graph Dense
-- statement:
--   Definitions and structural lemmas for St Variety Tangent Graph Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StVarietyTangentGraphDense.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
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
open MvPolynomial
noncomputable section
def VarietyTangentGraphDense.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ z ∈ zeroSetEuc J, ∀ ε : ℝ, 0 < ε →
      ∃ (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
        (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
        (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)) (w₀ : I₀ → ℂ),
        I₀.card = d ∧ IsOpen Ω ∧ IsOpen V ∧ w₀ ∈ Ω ∧ DifferentiableOn ℂ g Ω ∧
          (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ zeroSetEuc J ∩ V = g '' Ω ∧
          (∀ j ∉ I₀, fderiv ℂ (fun w => inner ℂ (b j) (g w)) w₀ = 0) ∧ dist (g w₀) z < ε
def VarietyTangentGraphDense.lineMap :
    (↥(Finset.univ : Finset (Fin 1)) → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin 1) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 1 => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j =>
      ContinuousLinearMap.proj (⟨j, Finset.mem_univ j⟩ : (Finset.univ : Finset (Fin 1))))
end
end GroundTheory.Heights₂.Heights


