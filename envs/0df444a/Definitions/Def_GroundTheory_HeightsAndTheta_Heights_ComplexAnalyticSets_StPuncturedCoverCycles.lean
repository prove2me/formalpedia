-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedCoverCycles
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedCoverCycles
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:40.355843+00:00
-- url     : https://prove2.me/theorems/e306213a-4226-42fc-8bd4-11f27a4005ac
-- title:
--   St Punctured Cover Cycles
-- statement:
--   Definitions and structural lemmas for St Punctured Cover Cycles, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPuncturedCoverCycles.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology Matrix
noncomputable section
def PuncturedCoverCycles.Statement : Prop :=
  ∀ (n e N : ℕ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (c : Fin (e + 1) → ℂ) (r : ℝ)
    (X : Set (Fin n → ℂ)),
    0 < r → c 0 = 0 →
    (∀ x ∈ X, dist (A *ᵥ x) c < r ∧ (A *ᵥ x) 0 ≠ 0) →
    (∀ y : Fin (e + 1) → ℂ, dist y c < r → y 0 ≠ 0 → {x | x ∈ X ∧ A *ᵥ x = y}.encard = N) →
    (∀ x ∈ X, ∃ (O : Set (Fin (e + 1) → ℂ)) (V' : Set (Fin n → ℂ)) (g : (Fin (e + 1) → ℂ) → Fin n → ℂ),
      IsOpen O ∧ A *ᵥ x ∈ O ∧ IsOpen V' ∧ x ∈ V' ∧ DifferentiableOn ℂ g O ∧ g (A *ᵥ x) = x ∧
        (∀ y ∈ O, A *ᵥ g y = y) ∧ X ∩ V' = g '' O) →
    ∃ (m : ℕ) (ord : Fin m → ℕ) (ψ : Fin m → (Fin (e + 1) → ℂ) → Fin n → ℂ) (δ : ℝ),
      0 < δ ∧ δ ≤ 1 ∧ ∑ b, ord b = N ∧ (∀ b, 1 ≤ ord b) ∧
      (∀ b, DifferentiableOn ℂ (ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0})) ∧
      (∀ b, ∀ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0},
        ψ b t ∈ X ∧ A *ᵥ ψ b t = Function.update t 0 (t 0 ^ ord b)) ∧
      (∀ b, Set.InjOn (ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0})) ∧
      (∀ b b', b ≠ b' → ∀ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0},
        ∀ t' ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}, ψ b t ≠ ψ b' t') ∧
      (∀ x ∈ X, dist (A *ᵥ x) c < δ ^ N →
        ∃ b, ∃ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}, ψ b t = x)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


