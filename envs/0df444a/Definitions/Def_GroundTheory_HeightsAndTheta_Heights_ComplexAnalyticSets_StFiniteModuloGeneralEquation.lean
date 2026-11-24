-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteModuloGeneralEquation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteModuloGeneralEquation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:20.598824+00:00
-- url     : https://prove2.me/theorems/b498f450-8dd4-4e31-923c-566a37b578bc
-- title:
--   St Finite Modulo General Equation
-- statement:
--   Definitions and structural lemmas for St Finite Modulo General Equation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFiniteModuloGeneralEquation.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteModuloEliminate
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
def FiniteModuloGeneralEquation.Statement : Prop :=
  ∀ (σ τ : Type) [Fintype σ] [Fintype τ] [DecidableEq τ] (x : σ → ℂ) (k : ℕ)
    (f : Fin k → (σ → ℂ) → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) (c : τ),
    (∀ i, AnalyticAt ℂ (f i) x) → IsFiniteModuloOver x f L →
    (∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : τ → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ c', AnalyticAt ℂ (h' c') x) ∧
      ∀ᶠ z in 𝓝 x, (L z c - L x c) ^ r =
        ∑ i, h i z * f i z + ∑ c', h' c' z * (zeroCoordinate c (L z) c' - zeroCoordinate c (L x) c')) →
    ∃ (d : ℕ) (F : (τ → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
      AnalyticAt ℂ F (L x) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
      (∀ᶠ z in 𝓝 x, F (L z) = ∑ i, h i z * f i z) ∧
      analyticOrderAt (fun s : ℂ => F (L x + Pi.single c s)) 0 = d
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


