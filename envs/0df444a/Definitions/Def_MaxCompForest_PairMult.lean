-- Prove2me | Definitions.Def_MaxCompForest_PairMult
-- name    : MaxCompForest_PairMult
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:32.670365+00:00
-- url     : https://prove2.me/theorems/17eeb4e9-5240-4803-acc2-b7476597ff97
-- title:
--   At most $\nu$ labels per vertex pair
-- statement:
--   A labelled multigraph has **pair multiplicity at most $\nu$** when every pair of distinct vertices is joined by at most $\nu$ labels, regardless of the size of their conductances.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma E.3, E.4, p.39

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **At most `ν` physical labels between any two distinct vertices.**
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Lemma E.3 and E.4, p.39. -/
def PairMult (H : WGraph V E) (ν : ℕ) : Prop :=
  ∀ a b : V, a ≠ b → (Finset.univ.filter fun e => s(H.head e, H.tail e) = s(a, b)).card ≤ ν

end MaxCompForest


