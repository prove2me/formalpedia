-- Prove2me | Definitions.Def_AvgValueAlloc_posVal
-- name    : AvgValueAlloc_posVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:00.400295+00:00
-- url     : https://prove2.me/theorems/1cc00000-c8ed-4ff1-ab2a-9e04dfcf62af
-- title:
--   Maximum positive value $P(v)$ and $P(A)$
-- statement:
--   For an item $v$, $P(v)=\max\{v_j:\ v_j\ge\rho_j\}$, or $0$ if $J(v)=\emptyset$; for a finite family $A$ of items (with multiplicity), $P(A)=\sum_{v\in A}P(v)$.
--
--   Positive-only allocation realizes $P(A)$ from zero surplus; $P$ is the currency in which validation errors are charged.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2, p.4

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_posSet

namespace AvgValueAlloc

/-- **Maximum positive value `P(v)` and `P(A)`.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2, p.4: "Let P(v) = max{v_j : v_j ≥ ρ_j}, or
zero if none, and P(A) = Σ_{v∈A} P(v)."

`posVal ρ v = max_{j ∈ J(v)} v_j` (`0` if `J(v) = ∅`); `posValSum ρ A = Σ_i P(A i)` for a finite
family of items (a multiset with multiplicity).

**Formalization Note.** The maximum is `Finset.sup` in `ℚ≥0`, whose bottom `0` is the stated
value for an empty `J(v)`. -/
def posVal {n : ℕ} (ρ : Fin n → ℚ) (v : Vec n) : ℚ≥0 := (posSet ρ v).sup v

/-- `P(A) = Σ_{v ∈ A} P(v)`. -/
noncomputable def posValSum {n : ℕ} {ι : Type} [Fintype ι] (ρ : Fin n → ℚ) (A : ι → Vec n) : ℝ :=
  ∑ i, ((posVal ρ (A i) : ℚ≥0) : ℝ)

end AvgValueAlloc


