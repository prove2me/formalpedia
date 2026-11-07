-- Prove2me | Definitions.Def_CutwidthCircuitLB_ROBP_IsAcceptingPath
-- name    : CutwidthCircuitLB_ROBP_IsAcceptingPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:27.941003+00:00
-- url     : https://prove2.me/theorems/322e199d-3b2f-4dec-bc85-f5fb0987d717
-- title:
--   Consistent start-to-accept path of a read-once program
-- statement:
--   A **start-to-accept path consistent with** $x \in \{0,1\}^n$ in a read-once program is a path through all $\ell$ transition layers that starts at the start vertex, ends at the accept vertex, and in each query layer tagged $x_j$ uses an edge labeled $x_j$.
--
--   **Formalization Note** A path is its sequence of vertices together with its choice of edge in every transition layer.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.2, p.7

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP
import Definitions.Def_CutwidthCircuitLB_ROBP_IsConsistentSegment

namespace CutwidthCircuitLB

/-- `(vs, es)` is a **start-to-accept path consistent with `x`** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.2, p.7): it
starts at the start vertex, ends at the accept vertex, and is consistent with `x` on every
transition layer. -/
def ROBP.IsAcceptingPath {n : ℕ} (R : ROBP n)
    (vs : (i : Fin (R.len + 1)) → Fin (R.layerSize i))
    (es : (t : Fin R.len) → Fin (R.edges t).length) (x : Fin n → Bool) : Prop :=
  vs 0 = R.start ∧ vs (Fin.last R.len) = R.accept ∧ R.IsConsistentSegment 0 R.len vs es x

end CutwidthCircuitLB


