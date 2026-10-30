-- Prove2me | Definitions.Def_GarberOLO_Alg3_alg3Call
-- name    : GarberOLO_Alg3_alg3Call
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:00:19.245979+00:00
-- url     : https://prove2.me/theorems/58647fca-b9d3-4e4c-b112-5344feeca5e6
-- title:
--   The Algorithm 2 call of round $t$ of Algorithm 3
-- statement:
--   In round $t \ge 1$, Algorithm 3 calls Algorithm 2 on $(y_{t+1}, \varepsilon)$. Its output gives $\tilde y_{t+1}$, the distribution $(a_1, \dots, a_N)$ and the oracle outputs $(v_i, s_i)$ from which $s_{t+1}$ is sampled, the loop count $k_t$, and the number of oracle calls made in round $t$.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Algorithm 3, line 8, p. 14

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_alg2
import Definitions.Def_GarberOLO_Alg3_alg3Input

namespace GarberOLO.Alg3

/-- **The Algorithm 2 call made in round t of Algorithm 3.**
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Algorithm 3, line 8, p. 14: "call Algorithm 2 with inputs (y_{t+1}, ε) to obtain an
approximated projection ỹ_{t+1}, a distribution (a₁, …, a_N) and {(v₁, s₁), …, (v_N, s_N)} ⊆
ℝᵈ × K, for some N ∈ ℕ."

`alg3Call S OK sel c s₁ η ε f t = alg2 S OK sel c ε y_{t+1}` for rounds `t ≥ 1`, with
`y_{t+1} = alg3Input … t`. Its `yt` is ỹ_{t+1} (`alg3Y … (t+1)`), its `a`, `vs` are the
distribution and oracle outputs from which s_{t+1} is sampled, its `loops` is the paper's k_t and
its `calls` the number of oracle calls of round t. -/
noncomputable def alg3Call {d : ℕ} (S : Setting d)
    (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (sel : (N : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin N → EuclideanSpace ℝ (Fin d)) → Fin N → ℝ)
    (c : ℝ) (s₁ : EuclideanSpace ℝ (Fin d)) (η ε : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) : Alg2Out d :=
  alg2 S OK sel c ε (alg3Input S OK sel c s₁ η ε f t)

end GarberOLO.Alg3


