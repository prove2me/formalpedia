-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetCover
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:44.982911+00:00
-- url     : https://prove2.me/theorems/4093a7e3-969d-4ab5-8309-d90ce4d415c5
-- title:
--   Statements Cone Sheet Cover
-- statement:
--   Definitions and structural lemmas for Statements Cone Sheet Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeSheetCover.lean

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
def ConeSheetCover.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n)))
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
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          {z : EuclideanSpace ℂ (Fin n) |
            (∀ q ∈ complexFibreIdeal P, eval (fun i => z i) q = 0) ∧
            Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 ≠ 0 ∧
            (Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0)⁻¹ •
                Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) ∉ ⋃ k, D k} = 0
end GroundTheory.Heights₂.Heights


