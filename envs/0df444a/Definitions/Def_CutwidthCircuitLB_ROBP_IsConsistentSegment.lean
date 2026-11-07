-- Prove2me | Definitions.Def_CutwidthCircuitLB_ROBP_IsConsistentSegment
-- name    : CutwidthCircuitLB_ROBP_IsConsistentSegment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:22.361347+00:00
-- url     : https://prove2.me/theorems/1be8fb01-11cb-4d12-aab7-06e896faed53
-- title:
--   Path segment of a read-once program consistent with an input
-- statement:
--   Let $R$ be a read-once program. A choice of one vertex in every layer and one edge in every transition layer forms, on the transition layers $t$ with $a \le t < b$, a **path consistent with the input** $x \in \{0,1\}^n$ if for each such $t$ the chosen edge goes from the chosen vertex of $V_t$ to the chosen vertex of $V_{t+1}$ and, when the layer is a query layer tagged $x_j$, its label is $x_j$.
--
--   **Formalization Note** Transition layers are indexed from $0$. An edge is chosen by its position in the layer's list of edges, so two parallel edges are two different choices. Layers outside $[a, b)$ are unconstrained.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.2, p.7

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP

namespace CutwidthCircuitLB

/-- The vertex sequence `vs` and edge choice `es` of a read-once program form, on the transition
layers `t` with `a ≤ t < b`, a path that is **consistent with the input `x`** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3),
Definition 2.2, p.7): the chosen edge of layer `t` goes from `vs t` to `vs (t + 1)`, and if layer `t`
is a query layer tagged `x_j`, its label is `x_j`.

**Formalization Note** Layers are 0-based: `t : Fin len` is the paper's transition layer `t + 1`.
`es t` indexes the list of edges of layer `t`, so parallel edges are distinct choices. Layers
outside `[a, b)` are unconstrained. -/
def ROBP.IsConsistentSegment {n : ℕ} (R : ROBP n) (a b : ℕ)
    (vs : (i : Fin (R.len + 1)) → Fin (R.layerSize i))
    (es : (t : Fin R.len) → Fin (R.edges t).length) (x : Fin n → Bool) : Prop :=
  ∀ t : Fin R.len, a ≤ t.val → t.val < b →
    ((R.edges t).get (es t)).1 = vs t.castSucc ∧ ((R.edges t).get (es t)).2.1 = vs t.succ ∧
      ∀ j : Fin n, R.tag t = some j → ((R.edges t).get (es t)).2.2 = x j

end CutwidthCircuitLB


