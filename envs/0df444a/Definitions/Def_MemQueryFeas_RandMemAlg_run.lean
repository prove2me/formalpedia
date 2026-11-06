-- Prove2me | Definitions.Def_MemQueryFeas_RandMemAlg_run
-- name    : MemQueryFeas_RandMemAlg_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:35.679616+00:00
-- url     : https://prove2.me/theorems/001fd7b2-f467-4c69-930e-5281d1cdfe96
-- title:
--   Run of a randomized algorithm against an adaptive oracle
-- statement:
--   Given an adaptive oracle $O$ and draws $\omega_0,\omega_1,\dots$, the run starts with the all-zero memory $\mathrm{Memory}_0=0$ and, in round $t$, queries $x_t=\psi_{query}(\mathrm{Memory}_t,\omega_t)$, receives $g_t=O(x_0,\dots,x_{t-1};x_t)$ and sets
--   $$
--   \mathrm{Memory}_{t+1}=\psi_{update}(\mathrm{Memory}_t,x_t,g_t,\omega_t).
--   $$
--   The run returns, for each $t$, the memory at the beginning of round $t$ and the list of earlier queries.
--
--   **Formalization Note** Rounds are numbered from $0$ (the paper's $\mathrm{Memory}_1$ is $\mathrm{Memory}_0$ here).
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_MemQueryFeas_RandMemAlg

namespace MemQueryFeas

/-- **Run of a randomized algorithm against an adaptive oracle.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF
p.4): "its memory state is initialized at `Memory_1 = 0`, and on each round it queries
`x_t = ψ_query(Memory_t)`, receives `g_t ∈ ℝ^d ∪ {Success}`, and then updates its memory state via
`Memory_{t+1} = ψ_update(Memory_t, x_t, g_t)`."

Given the draws `ω : ℕ → Ω` (one per round), `alg.run O ω t = (Memory_t, [x_0, …, x_{t-1}])`: the
memory at the beginning of round `t` and the queries made before it. In round `t` the query is
`x_t = query Memory_t (ω t)`, the response is `O [x_0, …, x_{t-1}] x_t`, and
`Memory_{t+1} = update Memory_t x_t (O … x_t) (ω t)`.

**Formalization Note.** Rounds are 0-based (`run 0` is the all-`false` memory and the empty
history). -/
noncomputable def RandMemAlg.run {d M : ℕ} (alg : RandMemAlg d M)
    (O : List (Vec d) → Vec d → Option (Vec d)) (ω : ℕ → alg.Ω) :
    ℕ → (Fin M → Bool) × List (Vec d)
  | 0 => (fun _ => false, [])
  | t + 1 =>
    let s := RandMemAlg.run alg O ω t
    let x := alg.query s.1 (ω t)
    (alg.update s.1 x (O s.2 x) (ω t), s.2 ++ [x])

end MemQueryFeas


