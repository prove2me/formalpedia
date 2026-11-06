-- Prove2me | Definitions.Def_IPMJumpLB_ArcU
-- name    : IPMJumpLB_ArcU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:11.062996+00:00
-- url     : https://prove2.me/theorems/deca58d2-f809-4964-8abd-e837ac4eefaa
-- title:
--   Arcs of the unit-demand shortest path instance
-- statement:
--   The arc set of the Section 4 instance with parameters $b, k \in \mathbb N$ consists of
--
--   1. for each gadget $0 \le i < k$, the forward arc $e_i^+ = (v_i, v_{i+1})$ and the backward arc $e_i^- = (v_{i+1}, v_i)$;
--   2. for each shortcut path $v_0 \to a_j \to v_k$, the two shortcut arcs $(v_0, a_j)$ and $(a_j, v_k)$;
--   3. one leaf arc from each leaf's parent to the leaf.
--
--   For $b \ge 1$ there are $\hat m_k = (2b-2)k^2 + k$ arcs.
--
--   **Formalization Note** An inductive type with constructors `fwd i`, `bwd i`, `scIn j`, `scOut j`, `leafArc i t` and `extraLeafArc t`, indexed as in `VertexU`; the gadget index $i$ is the paper's $0 \le i < k$.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Section 4, p.11 (main path and gadgets from Section 3.1, p.6)

import Mathlib

namespace IPMJumpLB

/-- The arcs of the unit-demand single-source shortest path instance of Section 4
(Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §4, p.11, building on §3.1, p.6), with parameters `b, k ∈ ℕ`:

* `fwd i`, `i < k`: the forward path arc `e⁺ᵢ = (vᵢ, vᵢ₊₁)` of gadget `i`;
* `bwd i`, `i < k`: the backward path arc `e⁻ᵢ = (vᵢ₊₁, vᵢ)` of gadget `i`;
* `scIn j`, `j < (b − 2)k²`: the first shortcut arc `(v₀, a_(j+1))`;
* `scOut j`, `j < (b − 2)k²`: the second shortcut arc `(a_(j+1), v_k)`;
* `leafArc i t`: the leaf arc from `v_(i+1)` to the leaf `leaf i t`;
* `extraLeafArc t`: the leaf arc from `v_k` to the leaf `extraLeaf t`.

**Formalization Note** Indices are 0-based, matching the paper's gadget index `0 ≤ i < k`. -/
inductive ArcU (b k : ℕ) where
  | fwd (i : Fin k)
  | bwd (i : Fin k)
  | scIn (j : Fin ((b - 2) * k ^ 2))
  | scOut (j : Fin ((b - 2) * k ^ 2))
  | leafArc (i : Fin k) (t : Fin (k - 1))
  | extraLeafArc (t : Fin (k ^ 2))
  deriving DecidableEq

/-- `ArcU b k` is in bijection with a sum of finite types (used for the `Fintype` instance). -/
def ArcU.equivSum (b k : ℕ) :
    ArcU b k ≃ Fin k ⊕ Fin k ⊕ Fin ((b - 2) * k ^ 2) ⊕ Fin ((b - 2) * k ^ 2) ⊕
      (Fin k × Fin (k - 1)) ⊕ Fin (k ^ 2) where
  toFun
    | .fwd i => .inl i
    | .bwd i => .inr (.inl i)
    | .scIn j => .inr (.inr (.inl j))
    | .scOut j => .inr (.inr (.inr (.inl j)))
    | .leafArc i t => .inr (.inr (.inr (.inr (.inl (i, t)))))
    | .extraLeafArc t => .inr (.inr (.inr (.inr (.inr t))))
  invFun
    | .inl i => .fwd i
    | .inr (.inl i) => .bwd i
    | .inr (.inr (.inl j)) => .scIn j
    | .inr (.inr (.inr (.inl j))) => .scOut j
    | .inr (.inr (.inr (.inr (.inl p)))) => .leafArc p.1 p.2
    | .inr (.inr (.inr (.inr (.inr t)))) => .extraLeafArc t
  left_inv := by intro e; cases e <;> rfl
  right_inv := by intro s; rcases s with i | i | j | j | ⟨i, t⟩ | t <;> rfl

instance (b k : ℕ) : Fintype (ArcU b k) := Fintype.ofEquiv _ (ArcU.equivSum b k).symm

end IPMJumpLB


