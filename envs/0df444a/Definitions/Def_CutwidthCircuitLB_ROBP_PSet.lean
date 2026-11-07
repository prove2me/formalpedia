-- Prove2me | Definitions.Def_CutwidthCircuitLB_ROBP_PSet
-- name    : CutwidthCircuitLB_ROBP_PSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:27.383201+00:00
-- url     : https://prove2.me/theorems/3fa31f81-fde0-4fdf-8020-a78247462143
-- title:
--   The set $P_v$ of past assignments reaching $v$
-- statement:
--   For a vertex $v \in V_i$ of a read-once program, $P_v$ is the set of assignments to the past of $V_i$ that admit a consistent path from the start vertex to $v$ (through the transition layers $1, \dots, i$).
--
--   **Formalization Note** $P_v$ is a set of assignments to the past variables only, not of full inputs: an assignment $p$ belongs to $P_v$ if some input extending $p$ is consistent with such a path. These layers query only past variables, so the choice of the extension does not matter.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.3, p.7

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP
import Definitions.Def_CutwidthCircuitLB_ROBP_IsConsistentSegment
import Definitions.Def_CutwidthCircuitLB_ROBP_past

namespace CutwidthCircuitLB

/-- `P_v` for a vertex `v ∈ V_i` of a read-once program (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.3, p.7): the set of
assignments to the past of `V_i` admitting a consistent path from start to `v`.

**Formalization Note** An element is an assignment `p` to the past variables only (a function on
the subtype `past i`), not a full input. `p` admits such a path if some input `x` extending `p` is
consistent with a path through the transition layers `t < i` from the start vertex to `v`; these
layers query only past variables, so the choice of the extension does not matter.
The path is recorded as a full vertex sequence and a choice of edge in every transition layer,
so the set is empty when some transition layer has no edges; such a program has no start-to-accept
path and accepts nothing, and Claim 2.1 and Lemma 2.2 read the same in that case. -/
def ROBP.PSet {n : ℕ} (R : ROBP n) (i : Fin (R.len + 1)) (v : Fin (R.layerSize i)) :
    Set ({j // j ∈ R.past i} → Bool) :=
  {p | ∃ x : Fin n → Bool, (∀ j : {j // j ∈ R.past i}, x j.1 = p j) ∧
    ∃ vs es, vs 0 = R.start ∧ vs i = v ∧ R.IsConsistentSegment 0 i.val vs es x}

end CutwidthCircuitLB


