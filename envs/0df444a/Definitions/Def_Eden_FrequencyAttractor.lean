-- Prove2me | Definitions.Def_Eden_FrequencyAttractor
-- name    : Eden_FrequencyAttractor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:14:54.556582+00:00
-- url     : https://prove2.me/theorems/df1df315-faf3-4b34-bdd7-cccb5550013c
-- title:
--   Frequency Attractor
-- statement:
--   Definitions and structural lemmas for Frequency Attractor, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyAttractor.lean

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_TorusAngles
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def FrequencyUniformlyAttractsBounded (c ν : ℝ) (C : Set PhaseSpace) : Prop :=
  ∀ B : Set PhaseSpace, Bornology.IsBounded B → ∀ ε : ℝ, 0 < ε →
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ p ∈ B,
      ∃ q ∈ C, dist (frequencyEvolution c ν t p) q < ε
def IsFrequencyGlobalAttractor (c ν : ℝ) (K : Set PhaseSpace) : Prop :=
  K.Nonempty ∧ IsCompact K ∧ (∀ t : ℝ, 0 ≤ t → frequencyEvolution c ν t '' K = K) ∧
    FrequencyUniformlyAttractsBounded c ν K
end Eden


