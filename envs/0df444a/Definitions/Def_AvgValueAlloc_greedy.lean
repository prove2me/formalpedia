-- Prove2me | Definitions.Def_AvgValueAlloc_greedy
-- name    : AvgValueAlloc_greedy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:39:25.277203+00:00
-- url     : https://prove2.me/theorems/56912ef2-5fda-4b4d-974c-ea7291861e59
-- title:
--   Exact greedy funding
-- statement:
--   Exact greedy processes the funding items in order. At item $v$, with $B$ the bank earned so far, it chooses a maximizing $j\in J(v)$ of the score $s_j$ of (6), with ties broken by the smallest original buyer index; when $J(v)=\emptyset$ it rejects the funding item.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2.1, p.5

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_posSet
import Definitions.Def_AvgValueAlloc_routBank
import Definitions.Def_AvgValueAlloc_Hobj

namespace AvgValueAlloc

open scoped Classical in
/-- The greedy choice at bank `B`: the least-index maximizer of the score over `J(u)`, or
rejection when `J(u) = ∅`. -/
noncomputable def greedyChoice {n : ℕ} (ρ : Fin n → ℚ) (V : (Fin n → ℝ) → ℝ) (B : Fin n → ℝ)
    (u : Vec n) : Option (Fin n) :=
  let best := (posSet ρ u).filter fun j => ∀ k ∈ posSet ρ u, score ρ V B u k ≤ score ρ V B u j
  if h : best.Nonempty then some (best.min' h) else none

/-- The greedy decisions on the first `t` funding items. -/
noncomputable def greedyList {n m : ℕ} (ρ : Fin n → ℚ) (V : (Fin n → ℝ) → ℝ)
    (M : Fin m → Vec n) : ℕ → List (Option (Fin n))
  | 0 => []
  | t + 1 =>
    let ds := greedyList ρ V M t
    ds ++ [if h : t < m then
      greedyChoice ρ V (prefBank ρ M (fun s => ds.getD s.val none) t) (M ⟨t, h⟩) else none]

/-- **Exact greedy funding.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2.1, p.5: "Exact greedy chooses a maximizing
j ∈ J(v), with ties by original buyer index; when J(v) is empty it rejects the funding item."

`greedy ρ V M t` is the decision on funding item `t`: with `B` the bank earned by the greedy
decisions on the earlier items, the least-index `j ∈ J(M t)` maximizing the score
`s_j = v_j + V(B + (v_j − ρ_j)e_j) − V(B)`, or rejection if `J(M t) = ∅`. -/
noncomputable def greedy {n m : ℕ} (ρ : Fin n → ℚ) (V : (Fin n → ℝ) → ℝ) (M : Fin m → Vec n) :
    Fin m → Option (Fin n) :=
  fun t => (greedyList ρ V M m).getD t.val none

end AvgValueAlloc


