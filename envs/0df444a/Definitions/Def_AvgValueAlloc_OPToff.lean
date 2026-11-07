-- Prove2me | Definitions.Def_AvgValueAlloc_OPToff
-- name    : AvgValueAlloc_OPToff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:12.069005+00:00
-- url     : https://prove2.me/theorems/c21e55b2-5f1d-446b-b3d2-59ad44f12332
-- title:
--   Final-feasible offline welfare $\mathrm{OPT}_{\mathrm{off}}(Q)$
-- statement:
--   For a live sequence $Q=(v_1,\dots,v_T)$,
--   $$
--   \mathrm{OPT}_{\mathrm{off}}(Q)=\max\Bigl\{W(Q,x):\ \textstyle\sum_{t:\,x_t=j}(v_{tj}-\rho_j)\ge0\ \text{for all } j\Bigr\},
--   $$
--   the best welfare of an assignment that satisfies only the final constraint. It depends only on the multiset of $Q$ and may use later sponsors for earlier assignments.
--
--   This is the offline benchmark of rows 2–4 of Table 1.
--
--   **Formalization Note** Values in $[0,\infty]$; the maximum is over a finite nonempty set (rejecting everything is feasible).
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_welfare
import Definitions.Def_AvgValueAlloc_prefixFeasible

namespace AvgValueAlloc

open scoped ENNReal

/-- **Final-feasible offline welfare `OPT_off(Q)`.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2: "Final-feasible offline welfare
OPT_off(Q) on live multiset Q may use later sponsors for earlier assignments; these benchmarks are
distinct."

`OPToff ρ Q = max welfare(Q, dec)` over all assignments `dec` of the items of `Q` to buyers (or
rejection) whose total surplus `Σ_{t: dec t = j} (v_{tj} − ρ_j)` is nonnegative for every buyer.

**Formalization Note.** `Q` is a sequence `Fin T → Vec n`; the value depends only on its multiset
of items. Only the final constraint is imposed (not (1)). Values in `ℝ≥0∞`; the supremum is over a
finite nonempty set (rejecting everything is feasible). -/
noncomputable def OPToff {n T : ℕ} (ρ : Fin n → ℚ) (Q : Fin T → Vec n) : ℝ≥0∞ :=
  ⨆ (dec : Fin T → Option (Fin n)) (_ : finalFeasible ρ Q dec), ENNReal.ofReal (welfare Q dec)

end AvgValueAlloc


