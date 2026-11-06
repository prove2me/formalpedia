-- Prove2me | Definitions.Def_MemQueryFeas_leafIdx
-- name    : MemQueryFeas_leafIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:22.028955+00:00
-- url     : https://prove2.me/theorems/3ac3d2da-3e28-4c45-b8a5-5db4a63bab76
-- title:
--   Current leaf of the transform oracle
-- statement:
--   The transform oracle starts at the first leaf $(1,\dots,1)$ and, at each query, advances its leaf as in Algorithm 4, line 3. The current leaf after the queries $x_0,\dots,x_{t-1}$ is obtained by applying this update to each of them in turn.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Algorithm 4, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_MemQueryFeas_advance

namespace MemQueryFeas

/-- **The transform oracle's current leaf.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Algorithm 4, p.9 (PDF p.10): "Throughout the
learning process the oracle keeps track of its current leaf `ℓ ∈ V_P`, initialized to the first leaf
`ℓ = (1, …, 1)`."

`leafIdx O N P h` is the index of the current leaf at the beginning of the round that follows the
queries `h = [x_0, …, x_{t−1}]`: start at `0` and apply `advance` for each past query.

**Formalization Note.** An index `N_1⋯N_P` means that the last leaf has been exhausted. -/
noncomputable def leafIdx {d : ℕ} (O : List ℕ → Vec d → Option (Vec d)) (N : ℕ → ℕ) (P : ℕ)
    (h : List (Vec d)) : ℕ :=
  h.foldl (fun n x => advance O N P n x) 0

end MemQueryFeas


