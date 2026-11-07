-- Prove2me | Definitions.Def_AvgValueAlloc_prefixFeasible
-- name    : AvgValueAlloc_prefixFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:00.961016+00:00
-- url     : https://prove2.me/theorems/588e20c4-abac-4d03-b078-75d119a1c8ab
-- title:
--   Prefix feasibility (1) and final feasibility
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$ be the thresholds. Decisions $x_1,\dots,x_T$ on items $v_1,\dots,v_T$ are **prefix feasible** if
--   $$
--   \sum_{s\le t:\ x_s=j}(v_{sj}-\rho_j)\ \ge 0\qquad (j\in[n],\ t\in[T]),\tag{1}
--   $$
--   and **final feasible** if this holds for $t=T$ only.
--
--   Prefix feasibility is the constraint every learner and every causal benchmark must meet: each buyer's average assigned value must stay at least its threshold at every prefix, starting from zero surplus. Final feasibility defines the offline benchmark, which may use later sponsors for earlier assignments.
--
--   **Formalization Note** Differences are computed in $\mathbb Q$.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2, eq. (1)

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec

namespace AvgValueAlloc

/-- **Prefix feasibility (1) and final feasibility.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2, (1): "with every prefix satisfying
Σ_{s≤t: s assigned to j} (v_{sj} − ρ_j) ≥ 0 (j ∈ [n], t ∈ [T])"; "Final-feasible offline welfare
OPT_off(Q) … may use later sponsors for earlier assignments".

`prefixFeasible ρ vs dec`: for every buyer `j` and every prefix end `t`, the assigned surplus
`Σ_{s ≤ t, dec s = some j} (v_{sj} − ρ_j)` is nonnegative. `finalFeasible ρ vs dec`: the same
only for the full horizon.

**Formalization Note.** Differences are computed in `ℚ` (`ρ : Fin n → ℚ`, values cast from
`ℚ≥0`), so no truncated subtraction occurs. -/
def prefixFeasible {n T : ℕ} (ρ : Fin n → ℚ) (vs : Fin T → Vec n)
    (dec : Fin T → Option (Fin n)) : Prop :=
  ∀ j : Fin n, ∀ t : Fin T,
    0 ≤ ∑ s ∈ Finset.univ.filter (fun s => s ≤ t ∧ dec s = some j), ((vs s j : ℚ) - ρ j)

/-- Final feasibility: the constraint (1) only at the last prefix. -/
def finalFeasible {n T : ℕ} (ρ : Fin n → ℚ) (vs : Fin T → Vec n)
    (dec : Fin T → Option (Fin n)) : Prop :=
  ∀ j : Fin n, 0 ≤ ∑ s ∈ Finset.univ.filter (fun s => dec s = some j), ((vs s j : ℚ) - ρ j)

end AvgValueAlloc


