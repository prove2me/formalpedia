-- Prove2me | Definitions.Def_JohnsonFlowShop_TwoStage_asapStart2
-- name    : JohnsonFlowShop_TwoStage_asapStart2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:36:35.01716+00:00
-- url     : https://prove2.me/theorems/6f6920e9-49cc-4dfd-80cd-83c516294faa
-- title:
--   Machine-2 start times of the as-soon-as-possible schedule of an order (p. 62)
-- statement:
--   Items are indexed by $i \in \{0,\dots,n-1\}$ (the paper's items $1,\dots,n$ shifted by one), and an order is a permutation $\sigma$ of the items with $\sigma(k)$ the item processed in position $k$ (positions $0,\dots,n-1$). In the **as-soon-as-possible schedule** of $\sigma$, each item starts on machine 2 as soon as both it has finished on machine 1 and machine 2 has finished the previous item. Write $C^1_k = \sum_{l \le k} A_{\sigma(l)}$ for the machine-1 completion time of position $k$, and define the machine-2 completion times of the first $m$ positions recursively by
--   $$
--   C^2_0 = 0, \qquad C^2_{m+1} = \max\bigl(C^1_m,\ C^2_m\bigr) + B_{\sigma(m)} \quad (m < n).
--   $$
--   Then item $i$, in position $k = \sigma^{-1}(i)$, starts on machine 2 at
--   $$
--   s^2_i = \max\bigl(C^1_k,\ C^2_k\bigr).
--   $$
--
--   **Formalization Note** `asapC2 A B σ m` is $C^2_m$ (it stays constant for $m \ge n$), and `asapStart2 A B σ i` is $s^2_i$.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 62, Two-stage production schedule ("we may start each item as soon as possible to minimize the total time")

import Mathlib

namespace JohnsonFlowShop.TwoStage

/-- `asapC2 A B σ m` is the time at which machine 2 finishes the items in the first `m`
positions of the order `σ` under the as-soon-as-possible schedule (`0` for `m = 0`):
the item in position `m` starts on machine 2 at the later of its completion time on machine 1,
`∑_{l ≤ m} A (σ l)`, and the machine-2 completion of the previous position (`0` if `m = 0`). -/
def asapC2 {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℕ → ℝ
  | 0 => 0
  | m + 1 =>
    if h : m < n then
      max (∑ l ∈ Finset.Iic (⟨m, h⟩ : Fin n), A (σ l)) (asapC2 A B σ m) + B (σ ⟨m, h⟩)
    else asapC2 A B σ m

/-- Machine-2 start times of the as-soon-as-possible schedule of the order `σ`: the item in
position `k = σ⁻¹ i` starts on machine 2 at the maximum of its completion time on machine 1,
`∑_{l ≤ k} A (σ l)`, and the machine-2 completion time of the item in the previous position. -/
def asapStart2 {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  max (∑ l ∈ Finset.Iic (σ.symm i), A (σ l)) (asapC2 A B σ (σ.symm i).val)

end JohnsonFlowShop.TwoStage


