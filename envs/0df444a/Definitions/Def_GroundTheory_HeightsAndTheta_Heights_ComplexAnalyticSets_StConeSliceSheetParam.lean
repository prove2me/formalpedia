-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSliceSheetParam
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSliceSheetParam
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:04:42.97623+00:00
-- url     : https://prove2.me/theorems/f42a05c6-e8b3-4bbd-a37e-5e2b8352914e
-- title:
--   St Cone Slice Sheet Param
-- statement:
--   Definitions and structural lemmas for St Cone Slice Sheet Param, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StConeSliceSheetParam.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGramLintegral
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
def ConeSliceSheetParam.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (A : Matrix (Fin e) (Fin n) ℂ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A →
      ∃ (U D : ℕ → Set (Fin e → ℂ)) (N : ℕ → ℕ)
        (s : (k : ℕ) → Fin (N k) → (Fin e → ℂ) → Fin n → ℂ),
        (∀ k, IsOpen (U k) ∧ MeasurableSet (D k) ∧ D k ⊆ U k ∧
          ∀ j, DifferentiableOn ℂ (s k j) (U k)) ∧
        Pairwise (Function.onFun Disjoint D) ∧
        volume (⋃ k, D k)ᶜ = 0 ∧
        (∀ k, ∀ y ∈ U k,
          ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y = Set.range (fun j => s k j y) ∧
          Function.Injective (fun j => s k j y) ∧
          ∀ j, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) (s k j)) ∧
        Set.InjOn (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
            q.2.2 • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s q.1.1 q.1.2 q.2.1))
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ∧
        (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
            q.2.2 • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s q.1.1 q.1.2 q.2.1)) ''
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ⊆
          {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} ∧
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          ({z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} \
            (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
              q.2.2 • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s q.1.1 q.1.2 q.2.1)) ''
              {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0}) = 0
end
end GroundTheory.Heights₂.Heights


