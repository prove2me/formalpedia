-- Prove2me | Definitions.Def_MemQueryFeas_DetMemAlg_run
-- name    : MemQueryFeas_DetMemAlg_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:58.626751+00:00
-- url     : https://prove2.me/theorems/28f67582-38bc-4551-933d-92442dc63c60
-- title:
--   Run of a deterministic algorithm against an adaptive oracle
-- statement:
--   Against an adaptive oracle $O$, the deterministic run starts from $\mathrm{Memory}_0=0$, queries $x_t=\psi_{query}(\mathrm{Memory}_t)$, receives $g_t=O(x_0,\dots,x_{t-1};x_t)$ and sets $\mathrm{Memory}_{t+1}=\psi_{update}(\mathrm{Memory}_t,x_t,g_t)$. It returns the memory at the beginning of each round together with the earlier queries.
--
--   **Formalization Note** Rounds are numbered from $0$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_MemQueryFeas_DetMemAlg

namespace MemQueryFeas

/-- **Run of a deterministic algorithm against an adaptive oracle.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF
p.4): "its memory state is initialized at `Memory_1 = 0`, and on each round it queries
`x_t = ψ_query(Memory_t)`, receives `g_t`, and then updates its memory state via
`Memory_{t+1} = ψ_update(Memory_t, x_t, g_t)`."

`alg.run O t = (Memory_t, [x_0, …, x_{t-1}])`, with `x_t = query Memory_t`, response
`O [x_0, …, x_{t-1}] x_t`, and `Memory_{t+1} = update Memory_t x_t (O … x_t)`.

**Formalization Note.** Rounds are 0-based; `run 0` is the all-`false` memory with empty history. -/
def DetMemAlg.run {d M : ℕ} (alg : DetMemAlg d M) (O : List (Vec d) → Vec d → Option (Vec d)) :
    ℕ → (Fin M → Bool) × List (Vec d)
  | 0 => (fun _ => false, [])
  | t + 1 =>
    let s := DetMemAlg.run alg O t
    let x := alg.query s.1
    (alg.update s.1 x (O s.2 x), s.2 ++ [x])

end MemQueryFeas


