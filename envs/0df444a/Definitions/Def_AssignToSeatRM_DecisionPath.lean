-- Prove2me | Definitions.Def_AssignToSeatRM_DecisionPath
-- name    : AssignToSeatRM_DecisionPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:17.306891+00:00
-- url     : https://prove2.me/theorems/b8c8e4c5-55d5-4768-8393-9d2394a82e5f
-- title:
--   Decision paths in the maximal-sequence state space: the update (8), $A^t$, $\gamma^{[t_1,t_2)}$ and $d^{[t_1,t_2)}$
-- statement:
--   Periods are $t=1,2,\dots$. In each period at most one request arrives. A **decision path** records, for each period, either that no request arrived, or the request $i\to j$ together with the maximal sequence $[u,v]$ ($u\le i\le j\le v$) it is put into, or its rejection, written $(0,i,j,0)$.
--
--   The **state** is the vector $A^t=(A^t_{uv})_{u\le v}$ of maximal-sequence counts at the beginning of period $t$. Putting $i\to j$ into $[u,v]$ changes it by (8):
--
--   $$A_{uv}\leftarrow A_{uv}-1,\qquad A_{u(i-1)}\leftarrow A_{u(i-1)}+1\ \text{ if } u<i,\qquad A_{(j+1)v}\leftarrow A_{(j+1)v}+1\ \text{ if } j<v;$$
--
--   a rejection or an empty period leaves it unchanged. A path is **feasible** on $[1,T]$ if every decision is an index of (14) and every allocation into $[u,v]$ happens when $A^t_{uv}\ge1$.
--
--   For $t_1\le t_2$, $d^{[t_1,t_2)}_{ij}$ is the number of periods $t\in[t_1,t_2)$ with a request $i\to j$, and $\gamma^{[t_1,t_2)}_{uijv}$ the number of periods in $[t_1,t_2)$ whose decision is $(u,i,j,v)$. The revenue of the path over $[1,T]$ is the sum of $p_{ij}$ over the accepted requests.
--
--   These objects carry the loss decomposition (EC.19) in the proof of Theorem 4; the path of RDP is a feasible decision path.
--
--   **Formalization Note** A path is `dec : ℕ → Option (ℕ×ℕ×ℕ×ℕ)`; `msState A¹ dec t` is $A^t$ for $t\ge1$.
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, (8) p.16; notation γ^{[t1,t2]}, d^{[t,t)}, A^t, p.ec18

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-! # Decision paths in the maximal-sequence state space

Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023, doi:10.1287/msom.2023.1188, the update
(8) (p.16) and the path notation of p.ec18 (`γ^{[t1,t2)}`, `d^{[t1,t2)}`, `A^t`).

**Formalization Note.**
1. Periods are `t = 1, 2, …`. A decision path is `dec : ℕ → Option Idx4`: `dec t = none` means
   that no request arrives in period `t`; `dec t = some (u, i, j, v)` means that a request
   `i → j` arrives and is put into a maximal sequence `[u, v]`; `some (0, i, j, 0)` means that
   it arrives and is rejected (p.ec18, "(u^t, i^t, j^t, v^t)"). At most one request arrives per
   period.
2. The state is the vector `A^t = (A^t_{uv})` of maximal-sequence counts, natural numbers.
   `msState A¹ dec t = A^t` for `t ≥ 1` (and `msState A¹ dec 0 = A¹`): putting `i → j` into
   `[u, v]` changes `A` by (8): `A_{uv} − 1`, `A_{u(i−1)} + 1` if `u < i`, `A_{(j+1)v} + 1` if
   `j < v`; a rejection or an empty period leaves it unchanged.
3. A path is *feasible* on `[1, T]` (`IsFeasPath`) if every decision is an index of (14) and
   every allocation goes into a maximal sequence that exists, `A^t_{u^t v^t} ≥ 1`. RDP's path is
   feasible (constraints (15)); the lemmas stated for feasible paths therefore cover it.
4. `demandCount dec t₁ t₂ i j = d^{[t₁,t₂)}_{ij}` and `gammaCount dec t₁ t₂ c = γ^{[t₁,t₂)}_c`
   count the periods in `[t₁, t₂)` with a request `i → j`, resp. with decision `c`. -/

/-- The update (8) (p.16) of the maximal-sequence counts when a request `i → j` is put into
`[u, v]` (`u ≥ 1`); a rejection `(0, i, j, 0)` leaves the counts unchanged. -/
def msUpdate (A : ℕ → ℕ → ℕ) (c : Idx4) : ℕ → ℕ → ℕ :=
  if c.1 = 0 then A else
  fun x y =>
    A x y - (if x = c.1 ∧ y = c.2.2.2 then 1 else 0)
      + (if c.1 < c.2.1 ∧ x = c.1 ∧ y = c.2.1 - 1 then 1 else 0)
      + (if c.2.2.1 < c.2.2.2 ∧ x = c.2.2.1 + 1 ∧ y = c.2.2.2 then 1 else 0)

/-- One period's transition of the maximal-sequence counts. -/
def msStep (A : ℕ → ℕ → ℕ) : Option Idx4 → (ℕ → ℕ → ℕ)
  | none => A
  | some c => msUpdate A c

/-- The maximal-sequence counts `A^t` at the beginning of period `t ≥ 1` along the decision
path `dec`, starting from `A¹`. -/
def msState (A₁ : ℕ → ℕ → ℕ) (dec : ℕ → Option Idx4) : ℕ → (ℕ → ℕ → ℕ)
  | 0 => A₁
  | t + 1 => if t = 0 then A₁ else msStep (msState A₁ dec t) (dec t)

/-- The decision path is feasible on the periods `1, …, T`: each decision is an index of (14)
(an allocation `u ≤ i ≤ j ≤ v` or a rejection `(0, i, j, 0)`), and each allocation into `[u, v]`
uses a maximal sequence that exists, `A^t_{uv} ≥ 1`. -/
def IsFeasPath (M T : ℕ) (A₁ : ℕ → ℕ → ℕ) (dec : ℕ → Option Idx4) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ c : Idx4, dec t = some c →
    c ∈ gammaIdx M ∧ (c.1 ≠ 0 → 1 ≤ msState A₁ dec t c.1 c.2.2.2)

/-- `d^{[t₁,t₂)}_{ij}`: the number of periods `t ∈ [t₁, t₂)` with a request `i → j`. -/
def demandCount (dec : ℕ → Option Idx4) (t₁ t₂ i j : ℕ) : ℕ :=
  ((Finset.Ico t₁ t₂).filter (fun t => ∃ u v : ℕ, dec t = some (u, i, j, v))).card

/-- `γ^{[t₁,t₂)}_{uijv}`: the number of periods `t ∈ [t₁, t₂)` whose decision is
`(u, i, j, v)` (p.ec18). -/
def gammaCount (dec : ℕ → Option Idx4) (t₁ t₂ : ℕ) (c : Idx4) : ℕ :=
  ((Finset.Ico t₁ t₂).filter (fun t => dec t = some c)).card

/-- The revenue collected along the path over the periods `1, …, T`: `p_{ij}` for every
accepted request `i → j`. -/
def pathRevenue (p : ℕ → ℕ → ℝ) (dec : ℕ → Option Idx4) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T,
    match dec t with
    | none => 0
    | some c => if c.1 = 0 then 0 else p c.2.1 c.2.2.1

end AssignToSeatRM


