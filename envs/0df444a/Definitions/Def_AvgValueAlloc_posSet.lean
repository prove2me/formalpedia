-- Prove2me | Definitions.Def_AvgValueAlloc_posSet
-- name    : AvgValueAlloc_posSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:08.236846+00:00
-- url     : https://prove2.me/theorems/8287c129-5439-408a-8682-aac6aa3c31b9
-- title:
--   Positive alternatives $J(v)$, sponsors and local sponsors
-- statement:
--   For an item $v$, its **positive alternatives** are $J(v)=\{j:\ v_j\ge\rho_j\}$ (including equality); $v$ is a **sponsor** if $J(v)\neq\emptyset$. A sponsor is **local** (its positive alternatives are locally comparable) if
--   $$
--   \max_{j\in J(v)}\rho_j<2\min_{j\in J(v)}\rho_j .
--   $$
--   A family of items is **all-local** when every sponsor in it is local; this is the local random-order class.
--
--   **Formalization Note** Locality is written as $\rho_i<2\rho_j$ for all $i,j\in J(v)$, which is equivalent for nonempty $J(v)$.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.2, p.2

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec

namespace AvgValueAlloc

/-- **Positive alternatives `J(v)`, sponsors, and locally comparable sponsors.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.2, p.2: "A sponsor has J(v) = {j : v_j ≥ ρ_j}
≠ ∅, including equality. Its positive alternatives are locally comparable (or local) if
max_{j∈J(v)} ρ_j < 2 min_{j∈J(v)} ρ_j. The local random-order class requires every sponsor to
satisfy this condition."

`posSet ρ v = J(v)`; `IsSponsor ρ v` says `J(v) ≠ ∅`; `IsLocal ρ v` says `ρ_i < 2ρ_j` for all
`i, j ∈ J(v)` (equivalent to `max < 2 min` when `J(v) ≠ ∅`); `AllSponsorsLocal ρ P` says every
sponsor among the items `P i` is local. -/
def posSet {n : ℕ} (ρ : Fin n → ℚ) (v : Vec n) : Finset (Fin n) :=
  Finset.univ.filter fun j => ρ j ≤ (v j : ℚ)

/-- A sponsor: an item with a positive alternative. -/
def IsSponsor {n : ℕ} (ρ : Fin n → ℚ) (v : Vec n) : Prop := (posSet ρ v).Nonempty

/-- Locally comparable positive alternatives. -/
def IsLocal {n : ℕ} (ρ : Fin n → ℚ) (v : Vec n) : Prop :=
  ∀ i ∈ posSet ρ v, ∀ j ∈ posSet ρ v, ρ i < 2 * ρ j

/-- Every sponsor in a family of items is local. -/
def AllSponsorsLocal {n : ℕ} {ι : Type} (ρ : Fin n → ℚ) (P : ι → Vec n) : Prop :=
  ∀ i, IsSponsor ρ (P i) → IsLocal ρ (P i)

end AvgValueAlloc


