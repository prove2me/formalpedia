-- Prove2me | Definitions.Def_Eden_Nontransitivity
-- name    : Eden_Nontransitivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:04:31.172594+00:00
-- url     : https://prove2.me/theorems/756e419f-49a5-58ce-8686-8581a0b901a7
-- title:
--   Nontransitivity
-- statement:
--   Definitions and structural lemmas for Nontransitivity, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Theorems.Thm_Eden_evolution_mem_attractor

set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def innerRadialRegion : Set PhaseSpace := {p | p ∈ attractor ∧ radiusSq₁ p < 1}
def outerRadialRegion : Set PhaseSpace := {p | p ∈ attractor ∧ 1 < radiusSq₁ p}
def unitRadialLevel : Set PhaseSpace := {p | p ∈ attractor ∧ radiusSq₁ p = 1}
def attractorEvolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : attractor) : attractor :=
  ⟨evolution c t p.val, evolution_mem_attractor c ht p.property⟩
end Eden


