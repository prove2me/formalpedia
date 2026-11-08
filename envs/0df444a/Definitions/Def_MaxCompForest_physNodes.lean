-- Prove2me | Definitions.Def_MaxCompForest_physNodes
-- name    : MaxCompForest_physNodes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:33.465286+00:00
-- url     : https://prove2.me/theorems/38a9f7f5-279d-46c6-b642-681b249c4fb8
-- title:
--   The nodes of the physical recursion, by depth
-- statement:
--   The set of nodes of the recursion at depth $d$, each identified with its set $S$ of included labels. The root is $\emptyset$; a branching node has a child $S\cup\{e\}$ for each label $e$ it branches on.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), proof of Lemma E.2, p.39

import Mathlib
import Definitions.Def_MaxCompForest_physNode__7b4b7e
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]

/-- **The nodes of the physical recursion at depth `d`**, as included label sets: the root is `∅`, and a
branching node `S` has one child `S ∪ {e}` per label `e` it branches on.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), proof of Lemma E.2, p.39. -/
noncomputable def physNodes (G : WGraph V E) (k : ℕ) (α : ℝ) (M0 q : ℕ) : ℕ → Finset (Finset E)
  | 0 => {∅}
  | d + 1 => (physNodes G k α M0 q d).biUnion fun S =>
      match physNode G k α M0 q S with
      | .branch L => L.image fun e => insert e S
      | _ => ∅

end MaxCompForest


