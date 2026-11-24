-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:10.317802+00:00
-- url     : https://prove2.me/theorems/4b57c8f7-3113-4718-aa42-12d12cb517af
-- title:
--   Statements Cone Sheet Param
-- statement:
--   Definitions and structural lemmas for Statements Cone Sheet Param, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeSheetParam.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)
def ConeSheetParam.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      ∃ (U D : ℕ → Set (Fin e → ℂ)) (N : ℕ → ℕ)
        (s : (k : ℕ) → Fin (N k) → (Fin e → ℂ) → (Σ k, PBlk n k) → ℂ),
        (∀ k, IsOpen (U k) ∧ MeasurableSet (D k) ∧ D k ⊆ U k ∧
          ∀ j, DifferentiableOn ℂ (s k j) (U k)) ∧
        Pairwise (Function.onFun Disjoint D) ∧
        volume (⋃ k, D k)ᶜ = 0 ∧
        (∀ k, ∀ x ∈ U k, fibre P Ψ x = Set.range (fun j => segre (s k j x)) ∧
          Function.Injective (fun j => segre (s k j x)) ∧
          ∀ j, IsSheet P Ψ x (segre (s k j x)) (s k j) ∧
            ∀ γ, IsSheet P Ψ x (segre (s k j x)) γ → γ =ᶠ[𝓝 x] s k j) ∧
        Set.InjOn (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
            q.2.2 • WithLp.toLp 2 (S *ᵥ fun i => s q.1.1 q.1.2 q.2.1 ⟨(), i⟩))
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ∧
        (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
            q.2.2 • WithLp.toLp 2 (S *ᵥ fun i => s q.1.1 q.1.2 q.2.1 ⟨(), i⟩)) ''
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ⊆
          coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) ∧
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          (coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) \
            (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
              q.2.2 • WithLp.toLp 2 (S *ᵥ fun i => s q.1.1 q.1.2 q.2.1 ⟨(), i⟩)) ''
              {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0}) = 0
end GroundTheory.Heights₂.Heights


