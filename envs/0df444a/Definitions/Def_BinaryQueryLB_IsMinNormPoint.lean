-- Prove2me | Definitions.Def_BinaryQueryLB_IsMinNormPoint
-- name    : BinaryQueryLB_IsMinNormPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:11.075976+00:00
-- url     : https://prove2.me/theorems/a0047554-2655-4832-8129-28f6062fce49
-- title:
--   A point of $K$ closest to the origin
-- statement:
--   A point $p$ is a **point of $K$ closest to the origin** if $p\in K$ and $\|p\|_2\le\|v\|_2$ for every $v\in K$. For $K=K_W$ the paper calls it $p_W$ and writes $h_W=\|p_W\|_2$.
--
--   **Formalization Note** A predicate, not a chosen point; for the compact convex $K_W$ there is exactly one such point, and theorems hold for every such $p$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.3, p.13

import Mathlib
import Definitions.Def_BinaryQueryLB_PtSpace

namespace BinaryQueryLB

/-- **A point of `K` closest to the origin.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.3, p.13: "let `p_W` be the point of `K_W`
closest to the origin. Write `h_W = ∥p_W∥₂`".

**Formalization Note.** A predicate rather than a chosen point; theorems quantify over every such
`p` (there is exactly one for the compact convex `K_W`), and `h_W` is `‖p‖`. -/
def IsMinNormPoint {m : ℕ} (K : Set (PtSpace m)) (p : PtSpace m) : Prop :=
  p ∈ K ∧ ∀ v ∈ K, ‖p‖ ≤ ‖v‖

end BinaryQueryLB


