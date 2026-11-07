-- Prove2me | Definitions.Def_AvgValueAlloc_Vec
-- name    : AvgValueAlloc_Vec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:36:21.982412+00:00
-- url     : https://prove2.me/theorems/d76e5e72-4af7-444a-96dd-c735630afe9e
-- title:
--   Item vector $v\in\mathbb Q_{\ge0}^n$
-- statement:
--   An **item** is a vector $v=(v_1,\dots,v_n)\in\mathbb Q_{\ge 0}^n$: coordinate $v_j$ is the value of the item to the original buyer $j\in[n]$. Coordinates of one item may be correlated arbitrarily.
--
--   Every live, historical, funding, information and service record of the paper is such a vector.
--
--   **Formalization Note** Buyers are indexed by `Fin n` (0-based). Differences $v_j-\rho_j$ are always computed after casting to $\mathbb Q$ or $\mathbb R$.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2 (laws on $\mathbb Q^n_+$)

import Mathlib

namespace AvgValueAlloc

/-- **An item: a vector of nonnegative rational values, one per original buyer.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2: "independent draws from an unknown
finite-support law D on Q^n_+. Coordinates within a vector may correlate."

`Vec n = Fin n → ℚ≥0`: coordinate `j` is the value `v_j` of the item to buyer `j`.

**Formalization Note.** Buyers are `Fin n` (0-based). Values are nonnegative rationals by type;
every difference `v_j − ρ_j` in the mission is computed after casting to `ℚ` or `ℝ`, never in
`ℚ≥0` (whose subtraction truncates). -/
abbrev Vec (n : ℕ) : Type := Fin n → ℚ≥0

end AvgValueAlloc


