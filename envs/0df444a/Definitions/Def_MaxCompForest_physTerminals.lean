-- Prove2me | Definitions.Def_MaxCompForest_physTerminals
-- name    : MaxCompForest_physTerminals
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:29.277429+00:00
-- url     : https://prove2.me/theorems/c870641a-9aff-4e62-a206-ac74d4421f6c
-- title:
--   Complete candidates of the recursion
-- statement:
--   All complete candidates returned by the terminal nodes of the recursion at depths $0,\dots,k$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma E.2, p.38

import Mathlib
import Definitions.Def_MaxCompForest_physNodes
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]

/-- **The complete candidates of the recursion**: all candidates returned by terminal nodes of depth at most
`k`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Lemma E.2, p.38. -/
noncomputable def physTerminals (G : WGraph V E) (k : ℕ) (α : ℝ) (M0 q : ℕ) : Finset (Finset E) :=
  (Finset.range (k + 1)).biUnion fun d => (physNodes G k α M0 q d).biUnion fun S =>
    match physNode G k α M0 q S with
    | .terminal c => c
    | _ => ∅

end MaxCompForest


