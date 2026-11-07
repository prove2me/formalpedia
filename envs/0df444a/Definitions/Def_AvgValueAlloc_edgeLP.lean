-- Prove2me | Definitions.Def_AvgValueAlloc_edgeLP
-- name    : AvgValueAlloc_edgeLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:17.744506+00:00
-- url     : https://prove2.me/theorems/16ae0611-397c-429a-ae09-0a3eb80c5376
-- title:
--   Service LP $F^J_A(B)$ of (5)
-- statement:
--   A **negative edge** of record $i$ at buyer $j$ has $0<v_{ij}<\rho_j$ and deficit $d_{ij}=\rho_j-v_{ij}$; it is **efficient** if $\rho_j/2\le v_{ij}<\rho_j$. For a buyer set $J$, records $A$ and banks $B\ge0$,
--   $$
--   F^J_A(B)=\max_{x\ge0}\Bigl\{\sum_{i\in A,\,j\in J}v_{ij}x_{ij}:\ \sum_{j\in J}x_{ij}\le1,\ \sum_{i\in A}d_{ij}x_{ij}\le B_j\Bigr\},\tag{5}
--   $$
--   with only efficient-negative variables. The maximum retained reward of a record is $\max\{v_j:\ j\in J,\ \rho_j/2\le v_j<\rho_j\}$ ($0$ if none).
--
--   This LP measures what a bank of earned surplus can buy in service.
--
--   **Formalization Note** Written as an LP over an arbitrary edge set (used also for the small-edge LP of the kernel); the value is a supremum over a nonempty compact polytope when $B\ge0$.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2, p.4; §2.1, p.4, eq. (5)

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec

namespace AvgValueAlloc

/-- Feasibility for the service LP (5) restricted to an edge set `E`: `x ≥ 0`, `x_{ij} = 0` off
`E`, `Σ_j x_{ij} ≤ 1` for every record, `Σ_i d_{ij} x_{ij} ≤ B_j` for every buyer, with deficit
`d_{ij} = ρ_j − v_{ij}`. -/
def LPFeasible {n : ℕ} {ι : Type} [Fintype ι] (ρ : Fin n → ℚ) (E : Vec n → Fin n → Prop)
    (A : ι → Vec n) (B : Fin n → ℝ) (x : ι → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ (∀ i j, ¬ E (A i) j → x i j = 0) ∧ (∀ i, ∑ j, x i j ≤ 1) ∧
    (∀ j, ∑ i, ((ρ j : ℝ) - ((A i j : ℚ≥0) : ℝ)) * x i j ≤ B j)

/-- The objective `Σ_{i,j} v_{ij} x_{ij}`. -/
noncomputable def LPValue {n : ℕ} {ι : Type} [Fintype ι] (A : ι → Vec n) (x : ι → Fin n → ℝ) :
    ℝ :=
  ∑ i, ∑ j, ((A i j : ℚ≥0) : ℝ) * x i j

/-- **The service LP value on a set of records, restricted to an edge set.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2.1, p.4, (5).

`edgeLP ρ E A B = max {Σ v_{ij} x_{ij} : x feasible}` (see `LPFeasible`).

**Formalization Note.** A `sSup` in `ℝ`; for `B ≥ 0` the feasible set is a nonempty compact
polytope (`x = 0` is feasible, `0 ≤ x ≤ 1`), so the value is the LP maximum. -/
noncomputable def edgeLP {n : ℕ} {ι : Type} [Fintype ι] (ρ : Fin n → ℚ)
    (E : Vec n → Fin n → Prop) (A : ι → Vec n) (B : Fin n → ℝ) : ℝ :=
  sSup {y : ℝ | ∃ x, LPFeasible ρ E A B x ∧ y = LPValue A x}

/-- Efficient negative edges into a buyer set `J`: `j ∈ J` and `ρ_j/2 ≤ v_j < ρ_j`. -/
def effEdge {n : ℕ} (ρ : Fin n → ℚ) (J : Finset (Fin n)) (u : Vec n) (j : Fin n) : Prop :=
  j ∈ J ∧ ρ j / 2 ≤ (u j : ℚ) ∧ (u j : ℚ) < ρ j

/-- **The service LP `F^J_A(B)` of (5).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2, p.4: "a negative has 0 < v_j < ρ_j and
original deficit d_ij = ρ_j − v_ij. Retain efficient negatives ρ_j/2 ≤ v_j < ρ_j"; §2.1, p.4, (5):
"F^J_A(B) = max_{x≥0} {Σ_{i∈A, j∈J} v_ij x_ij : Σ_{j∈J} x_ij ≤ 1, Σ_{i∈A} d_ij x_ij ≤ B_j}. Only
efficient-negative variables occur."

`Flp ρ J A B` is this LP on the records `A i` (with multiplicity) and banks `B`.

**Formalization Note.** Banks are real vectors; every statement takes `B ≥ 0`. -/
noncomputable def Flp {n : ℕ} {ι : Type} [Fintype ι] (ρ : Fin n → ℚ) (J : Finset (Fin n))
    (A : ι → Vec n) (B : Fin n → ℝ) : ℝ :=
  edgeLP ρ (effEdge ρ J) A B

open scoped Classical in
/-- A record's maximum retained reward: `max {v_j : j ∈ J, ρ_j/2 ≤ v_j < ρ_j}`, `0` if none. -/
noncomputable def maxRetained {n : ℕ} (ρ : Fin n → ℚ) (J : Finset (Fin n)) (u : Vec n) : ℝ :=
  ((((Finset.univ.filter fun j => effEdge ρ J u j).sup u : ℚ≥0)) : ℝ)

end AvgValueAlloc


