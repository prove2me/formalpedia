-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LocalParametrisation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LocalParametrisation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:06.098802+00:00
-- url     : https://prove2.me/theorems/1287ce0a-78e0-48ac-9157-e19e8c1f1459
-- title:
--   Local Parametrisation
-- statement:
--   Definitions and structural lemmas for Local Parametrisation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/LocalParametrisation.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
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
open Topology
def IsLocalParametrisation {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ) : Prop :=
  IsOpen B ∧ w ∈ X ∩ B ∧ IsOpen D ∧ IsPreconnected D ∧ Set.MapsTo A (X ∩ B) D ∧
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) ∧
    (∀ x ∈ X ∩ B, A x = A w → x = w) ∧
    AnalyticOnNhd ℂ δ D ∧ (∃ y ∈ D, δ y ≠ 0) ∧
    (∀ y ∈ D, δ y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = N) ∧
    (∀ x ∈ X ∩ B, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ X ∩ B ∩ V = g '' O) ∧
    X ∩ B ⊆ closure {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0}
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


