-- Prove2me | Definitions.Def_SeatInventory_Distinct_MarginalAllocation
-- name    : SeatInventory_Distinct_MarginalAllocation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:04:38.939593+00:00
-- url     : https://prove2.me/theorems/c3b7703f-a138-4048-a5a4-f4bf88913191
-- title:
--   Seat-by-class marginal revenues m_i(k), n-largest sets, and the linear program (4.5)
-- statement:
--   Consider a leg of capacity $n$ seats and fare classes $i$ with fares $f_i$ and request laws $p_i$. For each class $i$ and seat number $k\in\{1,\dots,n\}$ the pair $(i,k)$ stands for "the $k$-th seat sold in class $i$", and its **expected marginal revenue** is
--   $$
--   m_i(k) = f_i \cdot P[r_i \ge k],
--   $$
--   the average fare of class $i$ times the probability of selling $k$ or more seats in that class (p. 90). Write $D_n$ for the set of all such pairs.
--
--   1. A set $T \subseteq D_n$ is a **set of $n$ largest values** of $m$ if $|T| = n$ and every value $m_i(k)$ with $(i,k)\in T$ is at least every value $m_j(l)$ with $(j,l)\in D_n\setminus T$. With ties, several such sets exist.
--   2. A set $T$ of pairs determines the **allocation** $S^T_i = \#\{k : (i,k)\in T\}$, the number of seats of class $i$ it contains.
--   3. The **linear program (4.5)** has one variable $X_{ik}$ per pair: maximise $\sum_{(i,k)\in D_n} X_{ik}\, m_i(k)$ subject to $\sum X_{ik} \le n$ and $0 \le X_{ik} \le 1$. The definitions record its feasible set and its objective.
--
--   These objects state the marginal (incremental) approach to seat allocation among distinct fare classes surveyed in Sect. 4.2 of the thesis.
--
--   **Formalization Note** Classes form a finite type; pairs are elements of `ι × ℕ` restricted to `univ ×ˢ Icc 1 n`, so the seat index starts at 1 and $m_i(1)=f_i$. $m_i(k)$ is `emsr (f i) (d i) k` from the mission's demand model, with the integer reading $P[r\ge k]$.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, pp. 88-90, Sect. 4.2, Eq. (4.5)

import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel

namespace SeatInventory.Distinct

/-- The index set of the decision variables `X_ik` of the linear program (4.5) (Belobaba 1987,
pp. 88–90): pairs `(i, k)` of a fare class `i` and a seat number `k ∈ {1, …, n}`, `n` being the
capacity of the leg. -/
def seatPairs (ι : Type*) [Fintype ι] (n : ℕ) : Finset (ι × ℕ) :=
  Finset.univ ×ˢ Finset.Icc 1 n

/-- `m_i(k) = f_i · P[r_i ≥ k]`, the expected marginal revenue from selling the `k`-th seat in
class `i` (p. 90): the average fare of class `i` times the probability of selling `k` or more
seats in that class. -/
noncomputable def marginalRevenue {ι : Type*} (f : ι → ℝ) (d : ι → PMF ℕ) (x : ι × ℕ) : ℝ :=
  emsr (f x.1) (d x.1) x.2

/-- `T` is a set of `n` largest values of `m` among the elements of `D`: `T ⊆ D`, `|T| = n`, and
every value of `m` on `T` is at least every value of `m` on `D \ T`. With ties several such `T`
exist. -/
def IsTopN {α : Type*} (m : α → ℝ) (D T : Finset α) (n : ℕ) : Prop :=
  T ⊆ D ∧ T.card = n ∧ ∀ x ∈ T, ∀ y ∈ D, y ∉ T → m y ≤ m x

/-- The booking limits read off a set `T` of (class, seat) pairs: class `i` receives
`S_i = #{k : (i, k) ∈ T}` seats. -/
def allocationOf {ι : Type*} [DecidableEq ι] (T : Finset (ι × ℕ)) (i : ι) : ℕ :=
  (T.filter (fun x => x.1 = i)).card

/-- Feasibility for the linear program (4.5), p. 90, over the variables `X a`, `a ∈ D`:
`0 ≤ X a ≤ 1` and `Σ_{a ∈ D} X a ≤ n`. -/
def IsLPFeasible {α : Type*} (D : Finset α) (n : ℕ) (X : α → ℝ) : Prop :=
  (∀ a ∈ D, 0 ≤ X a ∧ X a ≤ 1) ∧ ∑ a ∈ D, X a ≤ (n : ℝ)

/-- The objective `Σ_{a ∈ D} X a · m a` of the linear program (4.5), p. 90. -/
noncomputable def lpObjective {α : Type*} (m : α → ℝ) (D : Finset α) (X : α → ℝ) : ℝ :=
  ∑ a ∈ D, X a * m a

end SeatInventory.Distinct


