-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularLocus
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularLocus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:18.206629+00:00
-- url     : https://prove2.me/theorems/78f155df-dfbd-4e0f-a2c3-9af765e45c5e
-- title:
--   Regular Locus
-- statement:
--   Definitions and structural lemmas for Regular Locus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RegularLocus.lean

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
open Topology Filter
def IsRegularPointOf {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) (x : σ → ℂ) : Prop :=
  x ∈ Y ∧ ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
    (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧
      (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O
def regLocus {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) : Set (σ → ℂ) :=
  {x | IsRegularPointOf Y x}
def seqWithLimit : Set (Fin 1 → ℂ) :=
  insert 0 (Set.range fun n : ℕ => fun _ : Fin 1 => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


