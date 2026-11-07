-- Prove2me | Definitions.Def_CutwidthCircuitLB_ROBP_QSet
-- name    : CutwidthCircuitLB_ROBP_QSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:43.922442+00:00
-- url     : https://prove2.me/theorems/5b6ab443-1519-45b3-8053-839f171f00df
-- title:
--   The set $Q_v$ of future assignments leading from $v$ to accept
-- statement:
--   For a vertex $v \in V_i$ of a read-once program, $Q_v$ is the set of assignments to the future of $V_i$ that admit a consistent path from $v$ to the accept vertex (through the transition layers $i+1, \dots, \ell$).
--
--   **Formalization Note** $Q_v$ is a set of assignments to the future variables only: an assignment $q$ belongs to $Q_v$ if some input extending $q$ is consistent with such a path.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.3, p.7

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP
import Definitions.Def_CutwidthCircuitLB_ROBP_IsConsistentSegment
import Definitions.Def_CutwidthCircuitLB_ROBP_past

namespace CutwidthCircuitLB

/-- `Q_v` for a vertex `v ∈ V_i` of a read-once program (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.3, p.7): the set of
assignments to the future of `V_i` (the complement of its past) admitting a consistent path from `v`
to accept.

**Formalization Note** An element is an assignment `q` to the future variables only (a function
on the subtype `(past i)ᶜ`). `q` admits such a path if some input `x` extending `q` is consistent
with a path through the transition layers `t ≥ i` from `v` to the accept vertex.
The path is recorded as a full vertex sequence and a choice of edge in every transition layer,
so the set is empty when some transition layer has no edges; such a program has no start-to-accept
path and accepts nothing, and Claim 2.1 and Lemma 2.2 read the same in that case. -/
def ROBP.QSet {n : ℕ} (R : ROBP n) (i : Fin (R.len + 1)) (v : Fin (R.layerSize i)) :
    Set ({j // j ∈ (R.past i)ᶜ} → Bool) :=
  {q | ∃ x : Fin n → Bool, (∀ j : {j // j ∈ (R.past i)ᶜ}, x j.1 = q j) ∧
    ∃ vs es, vs i = v ∧ vs (Fin.last R.len) = R.accept ∧ R.IsConsistentSegment i.val R.len vs es x}

end CutwidthCircuitLB


