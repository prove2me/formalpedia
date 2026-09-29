-- Prove2me | Definitions.Def_OnlinePrimalDual_GroupSteiner_probHits
-- name    : OnlinePrimalDual_GroupSteiner_probHits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:57:36.365466+00:00
-- url     : https://prove2.me/theorems/33c84c28-8dcd-4e5e-8c74-3d7fc1a429ff
-- title:
--   Probability the random cover intersects a given edge set
-- statement:
--   `probHits ρ S := ℙ[C ∩ S ≠ ∅]`, the probability that the random cover `C` drawn from `ρ`
--   contains at least one edge of a fixed finite edge set `S`; used with `S` the image of a
--   group's vertices under a vertex-to-incident-edge map, to state group coverage.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 231, Lemma 11.3

import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover

namespace OnlinePrimalDual.GroupSteiner

/-- The probability `ℙ[C ∩ S ≠ ∅]` that the random cover `C` drawn from `ρ` contains at least one
edge of a fixed finite edge set `S`. Used to state the probability that a group `g` is covered,
with `S` the image under a vertex-to-incident-edge map of `g`'s vertices (Buchbinder & Naor, FnT
TCS 2009, Lemma 11.3, p. 231: "the probability that there exists `vᵢ ∈ C`"). -/
def RandomCover.probHits {E : Type*} [Fintype E] [DecidableEq E] (ρ : RandomCover E)
    (S : Finset E) : ℝ :=
  ∑ C ∈ Finset.univ.filter (fun C => ∃ e ∈ S, e ∈ C), ρ.p C

end OnlinePrimalDual.GroupSteiner


