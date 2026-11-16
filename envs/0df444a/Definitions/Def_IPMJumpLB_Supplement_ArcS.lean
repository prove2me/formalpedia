-- Prove2me | Definitions.Def_IPMJumpLB_Supplement_ArcS
-- name    : IPMJumpLB_Supplement_ArcS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:48:43.235867+00:00
-- url     : https://prove2.me/theorems/653bc55a-ae25-4bb7-b635-551f2555bc4c
-- title:
--   Arcs $E_k$ of the Section 3.1 instance (path arcs $e_i^\pm$ and shortcut arcs)
-- statement:
--   For an integer $k$, the hard instance of Section 3.1 has the arc set $E_k$ consisting of
--
--   1. for each gadget $0 \le i < k$, a **forward arc** $e_i^+ = (v_i, v_{i+1})$ and a **backward arc** $e_i^- = (v_{i+1}, v_i)$ (the path arcs);
--   2. for each $1 \le j \le k^2$, the two **shortcut arcs** $(v_0, a_j)$ and $(a_j, v_k)$.
--
--   There are $m_k = 2k^2 + 2k$ arcs (Eq. (7)).
--
--   **Formalization Note** Constructors `fwd i`, `bwd i` ($i < k$) and `scIn j`, `scOut j` ($j < k^2$, the paper's shortcut index $j+1$). Tails and heads are assigned in the instance `minCostFlowInstance`. Decidable equality is derived, and the finite-type instance comes from an explicit bijection with a sum of four index sets.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), §3.1, p.6

import Mathlib

namespace IPMJumpLB

namespace Supplement

/-- The arc set `E_k` of the hard instance of Section 3.1
(Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §3.1, p.6), for an integer `k`:

* `fwd i`, `i < k`: the forward path arc `e⁺ᵢ = (vᵢ, vᵢ₊₁)` of gadget `i`;
* `bwd i`, `i < k`: the backward path arc `e⁻ᵢ = (vᵢ₊₁, vᵢ)` of gadget `i`;
* `scIn j`, `j < k²`: the first shortcut arc `(v₀, a_(j+1))`;
* `scOut j`, `j < k²`: the second shortcut arc `(a_(j+1), v_k)`.

**Formalization Note** Indices are 0-based, matching the paper's gadget index `0 ≤ i < k`; the
shortcut index `j` is the paper's `j + 1`. -/
inductive ArcS (k : ℕ) where
  | fwd (i : Fin k)
  | bwd (i : Fin k)
  | scIn (j : Fin (k ^ 2))
  | scOut (j : Fin (k ^ 2))
  deriving DecidableEq

/-- `ArcS k` is in bijection with `Fin k ⊕ Fin k ⊕ Fin (k²) ⊕ Fin (k²)` (used for the
`Fintype` instance). -/
def ArcS.equivSum (k : ℕ) : ArcS k ≃ Fin k ⊕ Fin k ⊕ Fin (k ^ 2) ⊕ Fin (k ^ 2) where
  toFun
    | .fwd i => .inl i
    | .bwd i => .inr (.inl i)
    | .scIn j => .inr (.inr (.inl j))
    | .scOut j => .inr (.inr (.inr j))
  invFun
    | .inl i => .fwd i
    | .inr (.inl i) => .bwd i
    | .inr (.inr (.inl j)) => .scIn j
    | .inr (.inr (.inr j)) => .scOut j
  left_inv := by intro e; cases e <;> rfl
  right_inv := by intro s; rcases s with i | i | j | j <;> rfl

instance (k : ℕ) : Fintype (ArcS k) := Fintype.ofEquiv _ (ArcS.equivSum k).symm

end Supplement

end IPMJumpLB


