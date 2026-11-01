-- Prove2me | Definitions.Def_AssignToSeatRM_Basic
-- name    : AssignToSeatRM_Basic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:25.4005+00:00
-- url     : https://prove2.me/theorems/ee39daf2-6b79-494d-8a42-24c1b5963fad
-- title:
--   Itineraries $i\to j$, capacity matrices $C\in\{0,1\}^{N\times M}$, maximal sequences, $M_{uv}(C)$, $f(C)$, NSE and strongly NSE
-- statement:
--   A train route has $M$ legs, numbered $1,\dots,M$, and $N$ seats. An **itinerary** $i\to j$ is a pair of legs with $1\le i\le j\le M$; it occupies legs $i,i+1,\dots,j$. The same index set $\{(u,v):1\le u\le v\le M\}$ is used for intervals of legs.
--
--   A **capacity matrix** is $C\in\{0,1\}^{N\times M}$, where $C_{k\ell}=1$ means that leg $\ell$ of seat $k$ is still free. By convention $C_{k0}=C_{k(M+1)}=0$ for every seat.
--
--   1. **Maximal sequence** (Definition 1). $[u,v]$ is a maximal sequence of seat $k$, written $[u,v]\sim C_k$, if $C_{ku}=\dots=C_{kv}=1$ and $C_{k(u-1)}=C_{k(v+1)}=0$: a maximal run of consecutive free legs of seat $k$. $[u,v]\sim C$ if it is a maximal sequence of some seat.
--   2. $M_{uv}(C)=\{k\in[N]:[u,v]\sim C_k\}$, and the projection (7) is $f(C)_{uv}=|M_{uv}(C)|$, the number of seats having $[u,v]$ as a maximal sequence.
--   3. **NSE** (Definition 2): any two maximal sequences $[u_1,v_1]$, $[u_2,v_2]$ in $C$ share an endpoint ($u_1=u_2$ or $v_1=v_2$) or do not overlap ($u_1>v_2$ or $v_1<u_2$). **Strongly NSE**: they share an endpoint or are strongly non-overlapping ($u_1>v_2+1$ or $v_1<u_2-1$).
--   4. Assigning a request $i\to j$ to seat $k$ turns legs $i,\dots,j$ of seat $k$ to $0$: $C\mapsto C-e_k^\top e_{ij}$.
--
--   These are the combinatorial objects of the assign-to-seat model: a request must be served by one seat that is free on all of its legs, so the state of a seat is described by its maximal sequences.
--
--   **Formalization Note** Seats and legs inside `CapMat N M = Fin N → Fin M → Bool` are 0-based; the accessor `cap C k ℓ` reads the paper's 1-based leg $\ell$ and returns `false` outside $1,\dots,M$, which is the padding. The index set `gammaIdx M` of the variables $\gamma_{uijv}$ ($1\le u\le i\le j\le v\le M$) and $\gamma_{0ij0}$ (rejections) of the dynamic primal (14) is also defined here.
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, §2 p.8 (legs, itineraries, capacity matrix, padding), Definition 1 and Definition 2 p.11, (7) p.15, (8) p.16, (14) p.19 (index set)

import Mathlib

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-! # Legs, itineraries, capacity matrices and maximal sequences

F. Zhu, S. Liu, R. Wang, Z. Wang, *Assign-to-Seat: Dynamic Capacity Control for Selling
High-Speed Train Tickets*, Manufacturing & Service Operations Management (2023),
doi:10.1287/msom.2023.1188: §2 (p.8), Definitions 1 and 2 (p.11), (7) (p.15), (8) (p.16).

**Formalization Note.**
1. *Legs* are the natural numbers `1, …, M` (p.8). An itinerary `i → j` is a pair `(i, j)` with
   `1 ≤ i ≤ j ≤ M`; `itins M` is the finite set of them, and `Itin M` the corresponding type.
   The same set indexes the pairs `(u, v)`, `u ≤ v`, of maximal sequences.
2. *Capacity matrices* `C ∈ {0,1}^{N×M}` are `CapMat N M = Fin N → Fin M → Bool`: seat `k`
   (0-based, `Fin N`) and leg `ℓ` (0-based in `Fin M`). The accessor `cap C k ℓ` reads leg `ℓ`
   in the paper's 1-based numbering and returns `false` outside `1, …, M`, which is the paper's
   padding `C_{k0} = C_{k(M+1)} = 0` (p.8, p.11).
3. The LP variables `γ_{uijv}` of (14) are indexed by quadruples `(u, i, j, v) : Idx4`; the
   rejection variable `γ_{0ij0}` is the quadruple `(0, i, j, 0)`, exactly as in the paper. -/

/-- The itineraries `i → j` with `1 ≤ i ≤ j ≤ M` (p.8). The same finite set indexes the pairs
`(u, v)` with `1 ≤ u ≤ v ≤ M` (maximal sequences, entries of `f(C)`). -/
def itins (M : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter (fun q => q.1 ≤ q.2)

/-- The type of itineraries `i → j`, `1 ≤ i ≤ j ≤ M`. -/
abbrev Itin (M : ℕ) := {q : ℕ × ℕ // q ∈ itins M}

/-- The pairs `(u, v)` with `u ≤ i ≤ j ≤ v` (and `1 ≤ u`, `v ≤ M`): the maximal-sequence types
into which a request `i → j` can be put. -/
def envs (M i j : ℕ) : Finset (ℕ × ℕ) :=
  (itins M).filter (fun uv => uv.1 ≤ i ∧ j ≤ uv.2)

/-- The itineraries `(i, j)` with `u ≤ i ≤ j ≤ v`: the requests that can be put into a maximal
sequence `[u, v]`. -/
def reqsIn (M u v : ℕ) : Finset (ℕ × ℕ) :=
  (itins M).filter (fun ij => u ≤ ij.1 ∧ ij.2 ≤ v)

/-- Quadruples `(u, i, j, v)` indexing the variables of the dynamic primal (14). -/
abbrev Idx4 := ℕ × ℕ × ℕ × ℕ

/-- The index set of the variables of (14) (p.19): the allocation variables `γ_{uijv}` with
`1 ≤ u ≤ i ≤ j ≤ v ≤ M` and the rejection variables `γ_{0ij0}` with `1 ≤ i ≤ j ≤ M`. -/
def gammaIdx (M : ℕ) : Finset Idx4 :=
  ((Finset.range (M + 1)) ×ˢ (Finset.range (M + 1)) ×ˢ (Finset.range (M + 1)) ×ˢ
      (Finset.range (M + 1))).filter
    (fun c => ((c.2.1, c.2.2.1) ∈ itins M ∧ (c.1, c.2.2.2) ∈ envs M c.2.1 c.2.2.1) ∨
      (c.1 = 0 ∧ c.2.2.2 = 0 ∧ (c.2.1, c.2.2.1) ∈ itins M))

/-- A capacity matrix `C ∈ {0,1}^{N×M}`: `C k ℓ = true` iff leg `ℓ` of seat `k` is available
(p.8). Seats and legs are 0-based here; use `cap` for the paper's 1-based legs. -/
abbrev CapMat (N M : ℕ) := Fin N → Fin M → Bool

/-- `C_{kℓ}` with the paper's 1-based leg `ℓ`, and the padding `C_{k0} = C_{k(M+1)} = 0` (p.8):
`false` for every `ℓ` outside `1, …, M`. -/
def cap {N M : ℕ} (C : CapMat N M) (k : Fin N) (ℓ : ℕ) : Bool :=
  if h : 1 ≤ ℓ ∧ ℓ ≤ M then C k ⟨ℓ - 1, by omega⟩ else false

/-- `C_{kℓ}` as the real number `0` or `1`. -/
def capR {N M : ℕ} (C : CapMat N M) (k : Fin N) (ℓ : ℕ) : ℝ :=
  if cap C k ℓ = true then 1 else 0

/-- Seat `k` is available on every leg `i, …, j` (`e_{ij} ⩽ C_k`). -/
def IsFreeOn {N M : ℕ} (C : CapMat N M) (k : Fin N) (i j : ℕ) : Prop :=
  ∀ ℓ ∈ Finset.Icc i j, cap C k ℓ = true

/-- Definition 1 (p.11): `[u, v]` is a maximal sequence of seat `k` in `C`, `[u, v] ∼ C_k`:
`C_{ku} = ⋯ = C_{kv} = 1` and `C_{k(u−1)} = C_{k(v+1)} = 0` (with the padding of `cap`).
It forces `1 ≤ u ≤ v ≤ M`. -/
def IsMaxSeq {N M : ℕ} (C : CapMat N M) (k : Fin N) (u v : ℕ) : Prop :=
  u ≤ v ∧ (∀ ℓ ∈ Finset.Icc u v, cap C k ℓ = true) ∧ cap C k (u - 1) = false ∧
    cap C k (v + 1) = false

/-- Definition 1 (p.11): `[u, v] ∼ C`, a maximal sequence of some seat. -/
def IsMaxSeqIn {N M : ℕ} (C : CapMat N M) (u v : ℕ) : Prop :=
  ∃ k, IsMaxSeq C k u v

/-- Definition 1 (p.11): `M_{uv}(C) = {k ∈ [N] | [u, v] ∼ C_k}`. -/
def maxSeqSeats {N M : ℕ} (C : CapMat N M) (u v : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun k => IsMaxSeq C k u v)

/-- The projection (7) (p.15): `f(C)_{uv} = |M_{uv}(C)|`, the number of seats having `[u, v]`
as a maximal sequence. -/
def fC {N M : ℕ} (C : CapMat N M) (u v : ℕ) : ℕ :=
  (maxSeqSeats C u v).card

/-- Definition 2 (p.11): `C` is NSE if any two maximal sequences `[u₁, v₁]`, `[u₂, v₂]` in `C`
share an endpoint or do not overlap (`u₁ > v₂` or `v₁ < u₂`). -/
def IsNSE {N M : ℕ} (C : CapMat N M) : Prop :=
  ∀ u₁ v₁ u₂ v₂ : ℕ, IsMaxSeqIn C u₁ v₁ → IsMaxSeqIn C u₂ v₂ →
    (u₁ = u₂ ∨ v₁ = v₂) ∨ (v₂ < u₁ ∨ v₁ < u₂)

/-- Definition 2 (p.11): `C` is strongly NSE if any two maximal sequences `[u₁, v₁]`, `[u₂, v₂]`
in `C` share an endpoint or are strongly non-overlapping (`u₁ > v₂ + 1` or `v₁ < u₂ − 1`). -/
def IsStronglyNSE {N M : ℕ} (C : CapMat N M) : Prop :=
  ∀ u₁ v₁ u₂ v₂ : ℕ, IsMaxSeqIn C u₁ v₁ → IsMaxSeqIn C u₂ v₂ →
    (u₁ = u₂ ∨ v₁ = v₂) ∨ (v₂ + 1 < u₁ ∨ v₁ + 1 < u₂)

/-- The capacity matrix after a request `i → j` is assigned to seat `k`:
`C − e_kᵀ e_{ij}` (p.13), i.e. legs `i, …, j` of seat `k` become unavailable. -/
def assignSeat {N M : ℕ} (C : CapMat N M) (k : Fin N) (i j : ℕ) : CapMat N M :=
  fun k' ℓ => if k' = k ∧ i ≤ ℓ.val + 1 ∧ ℓ.val + 1 ≤ j then false else C k' ℓ

end AssignToSeatRM


