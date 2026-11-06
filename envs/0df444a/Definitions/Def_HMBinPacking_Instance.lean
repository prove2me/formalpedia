-- Prove2me | Definitions.Def_HMBinPacking_Instance
-- name    : HMBinPacking_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:25.376343+00:00
-- url     : https://prove2.me/theorems/fbfad311-3a7a-4bad-9ac0-046966171bc0
-- title:
--   High-multiplicity Bin Packing instance $(B, d, s, a, b)$ and its feasibility
-- statement:
--   A **Bin Packing instance** consists of a capacity $B\in\mathbb Z_{\ge1}$, a number $d\ge1$ of item sizes, item sizes $s_1,\dots,s_d\in\mathbb Z_{\ge1}$, multiplicities $a_1,\dots,a_d\in\mathbb Z_{\ge0}$ and a bin bound $b\in\mathbb Z_{\ge0}$. The sizes need not be distinct and need not be at most $B$.
--
--   The instance is **feasible** if $a_i$ items of size $s_i$ for each $1\le i\le d$ can be packed into at most $b$ bins of capacity $B$: there is an assignment $f$ of the items to bins $1,\dots,b$ such that for every bin $j$
--   $$
--   \sum_{\text{items } x \text{ with } f(x)=j} s(x)\;\le\;B .
--   $$
--
--   This is the problem of the paper, with parameter $d$. Bins may stay empty, which is the "at most $b$" of the question; for $b=0$ the instance is feasible exactly when every $a_i=0$.
--
--   **Formalization Note** The item types are indexed by `Fin d`, and the items are the pairs $(i,k)$ with $k<a_i$. The instance is a record of numbers; its binary input encoding is the separate definition `encodeInstance`.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, §1, problem box 'Bin Packing', p.1 (input and question)

import Mathlib

namespace HMBinPacking

/-- **A Bin Packing instance** (the problem box of §1).
Koana, Kumabe, *High-Multiplicity Bin Packing is FPT*, arXiv:2609.16923v2, §1, problem box
"Bin Packing", p.1: "Input: A capacity B ∈ Z≥1, d ≥ 1 item sizes s1, . . . , sd ∈ Z≥1,
multiplicities a1, . . . , ad ∈ Z≥0, and a bin bound b ∈ Z≥0."

**Formalization Note.** The item types are indexed by `Fin d`. The box requires neither distinct
sizes nor `s i ≤ B`, and neither is imposed here. The numbers are values, not lists: how an
instance is written down (in binary) is fixed separately by `encodeInstance`. -/
structure Instance where
  /-- the bin capacity `B` -/
  B : ℕ
  /-- the number `d` of item sizes (the parameter) -/
  d : ℕ
  /-- the item sizes `s₁, …, s_d` -/
  s : Fin d → ℕ
  /-- the multiplicities `a₁, …, a_d` -/
  a : Fin d → ℕ
  /-- the bin bound `b` -/
  b : ℕ
  /-- `B ∈ ℤ≥1` -/
  B_pos : 0 < B
  /-- `d ≥ 1` -/
  d_pos : 0 < d
  /-- `sᵢ ∈ ℤ≥1` -/
  s_pos : ∀ i, 0 < s i

/-- **Feasibility of a Bin Packing instance** (the question of the problem box).
Koana, Kumabe, arXiv:2609.16923v2, §1, problem box "Bin Packing", p.1: "Question: Can aᵢ items of
size sᵢ for each 1 ≤ i ≤ d be packed into at most b bins of capacity B?"

`Feasible I` holds when there is an assignment `f` of the items to the bins `0, …, b − 1` such that
the total size of the items in every bin is at most `B`.

**Formalization Note.** The items are the pairs `⟨i, k⟩` with `k < aᵢ` (the `k`-th item of size
`sᵢ`). A map into `Fin b` may leave bins empty, which is exactly "at most `b` bins". For `b = 0`
the instance is feasible iff every `aᵢ = 0`. -/
def Feasible (I : Instance) : Prop :=
  ∃ f : (Σ i : Fin I.d, Fin (I.a i)) → Fin I.b,
    ∀ j : Fin I.b, ∑ x ∈ Finset.univ.filter (fun x => f x = j), I.s x.1 ≤ I.B

end HMBinPacking


