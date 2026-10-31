-- Prove2me | Definitions.Def_ResistantSets_IsFragile
-- name    : ResistantSets_IsFragile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:23.460554+00:00
-- url     : https://prove2.me/theorems/fabfb485-59b6-41e2-b610-39073e88e719
-- title:
--   Fragile set $F\subseteq\{0,1\}^3$
-- statement:
--   A set $F\subseteq\{0,1\}^3$ with
--   $$
--   F\cap\{000,100,010,001,101,011\}=\{101,011\},
--   $$
--   and any set isomorphic to such an $F$, is **fragile**. The points $110$ and $111$ are free, so there are four such base sets.
--
--   A fragile set is not resistant: its induced clutter with respect to the origin has the intersecting members $\{1,3\}$ and $\{2,3\}$. Fragile restrictions are one of the two excluded families in the characterization of resistance (Theorem 1.8).
--
--   **Formalization Note** The string $x_1x_2x_3$ is the point `![x₁, x₂, x₃]`.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.4, §1.1 (fragile sets, Figure 2)

import Mathlib
import Definitions.Def_ResistantSets_IsIso

namespace ResistantSets

/-- **Fragile set** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.1, p.4): "Take a set F ⊆ {0,1}³ such that
F ∩ {000, 100, 010, 001, 101, 011} = {101, 011}. We refer to F, and any set isomorphic to it, as
fragile."

**Formalization Note** The string `x₁x₂x₃` is the point `![x₁, x₂, x₃]` (`1` = `true`). The
points `110` and `111` are free, so there are four base sets `F`, and `IsFragile` is their
isomorphism closure in `{0,1}³`. -/
def IsFragile (F : Finset (Fin 3 → Bool)) : Prop :=
  ∃ F₀ : Finset (Fin 3 → Bool),
    F₀ ∩ {![false, false, false], ![true, false, false], ![false, true, false],
          ![false, false, true], ![true, false, true], ![false, true, true]} =
      {![true, false, true], ![false, true, true]} ∧
    IsIso F₀ F

end ResistantSets


