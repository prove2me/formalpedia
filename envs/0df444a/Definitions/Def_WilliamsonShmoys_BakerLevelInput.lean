-- Prove2me | Definitions.Def_WilliamsonShmoys_BakerLevelInput
-- name    : WilliamsonShmoys_BakerLevelInput
-- status  : Definition
-- author  : @bbchallenge_user
-- created : 2026-11-24T11:34:16.828109+00:00
-- url     : https://prove2.me/theorems/10f3618a-4216-40d2-92c0-f4489025a1cf
-- title:
--   RAM input augmented with Baker BFS levels mod $k$
-- statement:
--   The standard input state `planarRAMInput n k edge weight` of the mission's unit-cost RAM, with one block of $n$ extra natural cells filled in: cell $2+n^2+n+v$ holds $L(v) \bmod k$, where $L$ is the Baker BFS level (`bakerLevel`) in the graph of the adjacency table. These cells come right after the $n$-cell output bitmap and are zero in the plain input. Every other cell and the program counter $0$ are unchanged. This is the state after the breadth-first-search phase of Baker's technique (Williamson–Shmoys, Section 10.2, p. 270).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel

set_option autoImplicit false

namespace WilliamsonShmoys

/-- The standard RAM input `planarRAMInput n k edge weight`, augmented with the Baker BFS
levels reduced mod `k`: natural cell `2 + n² + n + v` holds `bakerLevel G v % k`, where
`G` is the graph of the adjacency table. These cells come right after the `n`-cell output
bitmap and are zero in the plain input. All other cells, and the program counter `0`,
agree with `planarRAMInput`. This is the state after Baker's breadth-first search
(Williamson–Shmoys, Section 10.2, p. 270) has written each vertex's level class. -/
noncomputable def bakerLevelInput (n k : ℕ) (edge : Fin n → Fin n → Bool)
    (weight : Fin n → ℝ) : PlanarRAMState :=
  { planarRAMInput n k edge weight with
    natMem := fun a =>
      if h : 2 + n * n + n ≤ a ∧ a < 2 + n * n + n + n then
        bakerLevel (SimpleGraph.fromRel (fun u v => edge u v = true))
          ⟨a - (2 + n * n + n), by omega⟩ % k
      else (planarRAMInput n k edge weight).natMem a }

end WilliamsonShmoys


