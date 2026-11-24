-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:49.8811+00:00
-- url     : https://prove2.me/theorems/ea49245e-498f-4fa6-b36f-46dbdc6807c8
-- title:
--   St Local Branched Covering
-- statement:
--   Definitions and structural lemmas for St Local Branched Covering, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLocalBranchedCovering.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicOnSubset
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
open MvPolynomial Topology
def LocalBranchedCovering.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ)),
    I.IsPrime → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    ∃ (k : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (W : Set (σ → ℂ)) (D : Set (Fin k → ℂ)) (m : ℕ)
      (δ : (Fin k → ℂ) → ℂ),
      IsOpen W ∧ w ∈ W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ IsOpen D ∧ A w ∈ D ∧
      (∀ z ∈ zeroSetIn I ∩ W, A z = A w → z = w) ∧
      (∀ z ∈ zeroSetIn I ∩ closure W, A z ∈ D → z ∈ W) ∧
      DifferentiableOn ℂ δ D ∧
      (∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, δ t ≠ 0) ∧
      (∀ y ∈ D, δ y ≠ 0 → ∃ (O : Set (Fin k → ℂ)) (s : Fin m → (Fin k → ℂ) → σ → ℂ),
        IsOpen O ∧ y ∈ O ∧ (∀ j, DifferentiableOn ℂ (s j) O) ∧
        ∀ y' ∈ O, (∀ j, s j y' ∈ zeroSetIn I ∩ W ∧ A (s j y') = y') ∧
          Function.Injective (fun j => s j y') ∧
          ∀ z ∈ zeroSetIn I ∩ W, A z = y' → z ∈ Set.range (fun j => s j y')) ∧
      ∀ z ∈ zeroSetIn I ∩ W, ∀ ε > 0, A '' (zeroSetIn I ∩ Metric.ball z ε) ∈ 𝓝 (A z)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


