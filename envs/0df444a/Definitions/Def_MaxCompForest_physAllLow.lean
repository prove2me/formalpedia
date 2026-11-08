-- Prove2me | Definitions.Def_MaxCompForest_physAllLow
-- name    : MaxCompForest_physAllLow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:40:03.640805+00:00
-- url     : https://prove2.me/theorems/bc3f6f16-839f-4305-87aa-cdbc18aea131
-- title:
--   All-low nodes of the recursion
-- statement:
--   The set of nodes of the recursion, at depths $0,\dots,k$, at which it stops because every remaining label has transfer-current diagonal below $\alpha$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma E.2, p.38

import Mathlib
import Definitions.Def_MaxCompForest_physNodes
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]

/-- **The all-low nodes of the recursion** at depth at most `k`: the forests `S` where it stops with
`p_max < α`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Lemma E.2, p.38. -/
noncomputable def physAllLow (G : WGraph V E) (k : ℕ) (α : ℝ) (M0 q : ℕ) : Finset (Finset E) :=
  (Finset.range (k + 1)).biUnion fun d => (physNodes G k α M0 q d).biUnion fun S =>
    match physNode G k α M0 q S with
    | .allLow => {S}
    | _ => ∅

end MaxCompForest


