-- Prove2me | Definitions.Def_Eden_UniformAttraction
-- name    : Eden_UniformAttraction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:14:20.457905+00:00
-- url     : https://prove2.me/theorems/ef60a712-40a2-56a9-bf76-57329066442c
-- title:
--   Uniform Attraction
-- statement:
--   Definitions and structural lemmas for Uniform Attraction, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
namespace Eden
def attractionBound (c M W t : ℝ) : ℝ :=
  2 * (radiusEvolution t M - Real.sqrt 2) ^ 2 + W ^ 2 * Real.exp (-2 * c * t)
def UniformlyAttractsBounded (c : ℝ) (C : Set PhaseSpace) : Prop :=
  ∀ B : Set PhaseSpace, Bornology.IsBounded B → ∀ ε : ℝ, 0 < ε →
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ p ∈ B,
      ∃ q ∈ C, dist (evolution c t p) q < ε
def IsGlobalAttractor (c : ℝ) (K : Set PhaseSpace) : Prop :=
  K.Nonempty ∧ IsCompact K ∧ (∀ t : ℝ, 0 ≤ t → evolution c t '' K = K) ∧
    UniformlyAttractsBounded c K
end Eden


