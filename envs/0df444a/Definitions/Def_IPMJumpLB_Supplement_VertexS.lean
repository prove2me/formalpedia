-- Prove2me | Definitions.Def_IPMJumpLB_Supplement_VertexS
-- name    : IPMJumpLB_Supplement_VertexS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:48:26.935079+00:00
-- url     : https://prove2.me/theorems/fa96e20f-13e8-456e-ab1a-bff9b4cc40b0
-- title:
--   Vertices $V_k = \{v_0, \dots, v_k\} \cup \{a_1, \dots, a_{k^2}\}$ of the Section 3.1 instance
-- statement:
--   For an integer $k$, the hard instance of Section 3.1 has the vertex set
--   $$
--   V_k = \{v_0, v_1, \dots, v_k\} \cup \{a_1, \dots, a_{k^2}\}.
--   $$
--   The vertices $v_0, \dots, v_k$ form the **main path**; each $a_j$ is the middle vertex of the $j$-th **shortcut path** $v_0 \to a_j \to v_k$. There are $n_k = k^2 + k + 1$ vertices (Eq. (7)).
--
--   **Formalization Note** The type has two constructors: `path i` for $v_i$, $i \in \{0, \dots, k\}$, and `shortcut j` for $a_{j+1}$, $j \in \{0, \dots, k^2 - 1\}$ (0-based). Decidable equality is derived, and the finite-type instance comes from an explicit bijection with $\{0,\dots,k\} \sqcup \{0, \dots, k^2-1\}$.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), §3.1, p.6

import Mathlib

namespace IPMJumpLB

namespace Supplement

/-- The vertex set `V_k = {v₀, …, v_k} ∪ {a₁, …, a_(k²)}` of the hard instance of Section 3.1
(Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §3.1, p.6), for an integer `k`:

* `path i`, `i = 0, …, k`: the vertex `vᵢ` of the main path;
* `shortcut j`, `j < k²`: the middle vertex `a_(j+1)` of the `(j+1)`-st shortcut path.

**Formalization Note** Indices are 0-based: `shortcut j` is the paper's `a_(j+1)`. -/
inductive VertexS (k : ℕ) where
  | path (i : Fin (k + 1))
  | shortcut (j : Fin (k ^ 2))
  deriving DecidableEq

/-- `VertexS k` is in bijection with `Fin (k + 1) ⊕ Fin (k²)` (used for the `Fintype` instance). -/
def VertexS.equivSum (k : ℕ) : VertexS k ≃ Fin (k + 1) ⊕ Fin (k ^ 2) where
  toFun
    | .path i => .inl i
    | .shortcut j => .inr j
  invFun
    | .inl i => .path i
    | .inr j => .shortcut j
  left_inv := by intro v; cases v <;> rfl
  right_inv := by intro s; rcases s with i | j <;> rfl

instance (k : ℕ) : Fintype (VertexS k) := Fintype.ofEquiv _ (VertexS.equivSum k).symm

end Supplement

end IPMJumpLB


