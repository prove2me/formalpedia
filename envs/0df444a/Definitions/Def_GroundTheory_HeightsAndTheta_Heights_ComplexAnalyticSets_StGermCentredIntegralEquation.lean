-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermCentredIntegralEquation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermCentredIntegralEquation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:40.400881+00:00
-- url     : https://prove2.me/theorems/4a1cacd9-2c03-4d4a-99d1-49ad946d6451
-- title:
--   St Germ Centred Integral Equation
-- statement:
--   Definitions and structural lemmas for St Germ Centred Integral Equation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGermCentredIntegralEquation.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermPrimitivePresentation
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
open Topology Filter
def CentredIntegralEquation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    (∀ i, AnalyticAt ℂ (p i) w) →
    (∀ i : σ, ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
      IsGermCombination w p (fun z => z i ^ n + ∑ j, b j (A z) * z i ^ (j : ℕ))) →
    (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
      ∃ (s : Finset (σ → ℕ)) (a : (σ → ℕ) → (Fin d → ℂ) → ℂ), (∀ m ∈ s, AnalyticAt ℂ (a m) (A w)) ∧
        IsGermCombination w p (fun z => g z - ∑ m ∈ s, a m (A z) * ∏ i, z i ^ m i)) →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
      ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        IsGermCombination w p (fun z => g z ^ n + ∑ j, b j (A z) * g z ^ (j : ℕ)) ∧
        ∀ T : ℂ, T ^ n + ∑ j, b j (A w) * T ^ (j : ℕ) = (T - g w) ^ n
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


