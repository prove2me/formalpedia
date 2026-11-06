-- Prove2me | Definitions.Def_MemQueryFeas_DetMemAlg_runN
-- name    : MemQueryFeas_DetMemAlg_runN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:50.245386+00:00
-- url     : https://prove2.me/theorems/e0c60497-50df-4379-9d1d-9c55b60f650c
-- title:
--   Run of a deterministic algorithm against a non-adaptive oracle
-- statement:
--   Against a non-adaptive oracle $(O_t)_{t\ge0}$, the deterministic run starts from $\mathrm{Memory}_0=0$ and sets $\mathrm{Memory}_{t+1}=\psi_{update}(\mathrm{Memory}_t,x_t,O_t(x_t))$ with $x_t=\psi_{query}(\mathrm{Memory}_t)$.
--
--   **Formalization Note** Rounds are numbered from $0$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4); Theorem 1, p.2

import Mathlib
import Definitions.Def_MemQueryFeas_DetMemAlg

namespace MemQueryFeas

/-- **Run of a deterministic algorithm against a non-adaptive oracle.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Problem setup, p.3
(PDF p.4) and Theorem 1, p.2: the memory recursion `Memory_{t+1} = ψ_update(Memory_t, x_t, g_t)` with
`x_t = ψ_query(Memory_t)`, where now `g_t = O_t(x_t)` for a fixed sequence of response maps.

`alg.runN O t` is the memory at the beginning of round `t` (0-based), starting from all-`false`. -/
def DetMemAlg.runN {d M : ℕ} (alg : DetMemAlg d M) (O : ℕ → Vec d → Option (Vec d)) :
    ℕ → (Fin M → Bool)
  | 0 => fun _ => false
  | t + 1 =>
    let m := DetMemAlg.runN alg O t
    alg.update m (alg.query m) (O t (alg.query m))

end MemQueryFeas


