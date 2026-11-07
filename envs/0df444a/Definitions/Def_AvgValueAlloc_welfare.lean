-- Prove2me | Definitions.Def_AvgValueAlloc_welfare
-- name    : AvgValueAlloc_welfare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:08.487452+00:00
-- url     : https://prove2.me/theorems/c44ecee2-7c53-48be-809e-63d685e74098
-- title:
--   Welfare of an assignment
-- statement:
--   For items $v_1,\dots,v_T$ and decisions $x_t\in\{\text{reject}\}\cup[n]$, the **welfare** is the total original assigned value
--   $$
--   W=\sum_{t:\ x_t=j\neq\text{reject}} v_{t j}.
--   $$
--   The same function gives the welfare $W(X)$ of a funding routing $X$.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2; §2.1, p.5

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec

namespace AvgValueAlloc

/-- **Welfare of an assignment.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2: "Welfare is total original assigned
live value"; §2.1, p.5: "Its original welfare is W(X)".

For items `vs t` (`t : Fin T`) and decisions `dec t : Option (Fin n)` (`none` rejects, `some j`
assigns to buyer `j`), `welfare vs dec = Σ_{t : dec t = some j} v_{t j}`.

**Formalization Note.** The same function gives the welfare `W(X)` of a funding routing `X`. -/
noncomputable def welfare {n T : ℕ} (vs : Fin T → Vec n) (dec : Fin T → Option (Fin n)) : ℝ :=
  ∑ t, (dec t).elim 0 (fun j => ((vs t j : ℚ≥0) : ℝ))

end AvgValueAlloc


