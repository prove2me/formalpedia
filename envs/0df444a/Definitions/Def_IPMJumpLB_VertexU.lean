-- Prove2me | Definitions.Def_IPMJumpLB_VertexU
-- name    : IPMJumpLB_VertexU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:10.138703+00:00
-- url     : https://prove2.me/theorems/bb421a1a-0d31-494c-b72f-00eef6a003b2
-- title:
--   Vertices of the unit-demand shortest path instance
-- statement:
--   The vertex set of the Section 4 instance with parameters $b, k \in \mathbb N$ consists of
--
--   1. the main path vertices $v_0, \dots, v_k$;
--   2. one middle vertex $a_j$ for each of the $(b-2)k^2$ shortcut paths;
--   3. $k - 1$ leaves attached to each of $v_1, \dots, v_k$;
--   4. a further $k^2$ leaves attached to $v_k$.
--
--   For $b \ge 2$ there are $\hat n_k = bk^2 + 1$ vertices.
--
--   **Formalization Note** An inductive type with constructors `path i` ($i \le k$), `shortcut j` ($j < (b-2)k^2$, the vertex $a_{j+1}$), `leaf i t` ($i < k$, $t < k-1$, a leaf of $v_{i+1}$) and `extraLeaf t` ($t < k^2$, a leaf of $v_k$); all indices are 0-based. The `Fintype` instance comes from a bijection with a sum of `Fin` types.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Section 4, p.11 (main path from Section 3.1, p.6)

import Mathlib

namespace IPMJumpLB

/-- The vertices of the unit-demand single-source shortest path instance of Section 4
(Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §4, p.11, building on §3.1, p.6), with parameters `b, k ∈ ℕ`:

* `path i`, `i = 0, …, k`: the vertices `v₀, …, v_k` of the main path;
* `shortcut j`, `j < (b − 2)k²`: the middle vertex `a_(j+1)` of the `(j+1)`-st shortcut path;
* `leaf i t`, `i < k`, `t < k − 1`: the `(t+1)`-st of the `k − 1` leaves attached to `v_(i+1)`;
* `extraLeaf t`, `t < k²`: the `(t+1)`-st of the further `k²` leaves attached to `v_k`.

**Formalization Note** All indices are 0-based; `leaf i t` hangs on `v_(i+1)`, so the leaves
attached to `v₁, …, v_k` are `leaf 0 _, …, leaf (k−1) _`. -/
inductive VertexU (b k : ℕ) where
  | path (i : Fin (k + 1))
  | shortcut (j : Fin ((b - 2) * k ^ 2))
  | leaf (i : Fin k) (t : Fin (k - 1))
  | extraLeaf (t : Fin (k ^ 2))
  deriving DecidableEq

/-- `VertexU b k` is in bijection with a sum of finite types (used for the `Fintype` instance). -/
def VertexU.equivSum (b k : ℕ) :
    VertexU b k ≃ Fin (k + 1) ⊕ Fin ((b - 2) * k ^ 2) ⊕ (Fin k × Fin (k - 1)) ⊕ Fin (k ^ 2) where
  toFun
    | .path i => .inl i
    | .shortcut j => .inr (.inl j)
    | .leaf i t => .inr (.inr (.inl (i, t)))
    | .extraLeaf t => .inr (.inr (.inr t))
  invFun
    | .inl i => .path i
    | .inr (.inl j) => .shortcut j
    | .inr (.inr (.inl p)) => .leaf p.1 p.2
    | .inr (.inr (.inr t)) => .extraLeaf t
  left_inv := by intro v; cases v <;> rfl
  right_inv := by intro s; rcases s with i | j | ⟨i, t⟩ | t <;> rfl

instance (b k : ℕ) : Fintype (VertexU b k) := Fintype.ofEquiv _ (VertexU.equivSum b k).symm

end IPMJumpLB


