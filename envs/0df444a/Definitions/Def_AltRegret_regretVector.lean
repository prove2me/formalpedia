-- Prove2me | Definitions.Def_AltRegret_regretVector
-- name    : AltRegret_regretVector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:05:57.797207+00:00
-- url     : https://prove2.me/theorems/62da0062-f61f-4954-bc51-df2747780eea
-- title:
--   The alternating regret vector $R_t$ of the algorithm
-- statement:
--   For the alternation-aware Hedge algorithm with parameters $(\eta,\beta)$ and plays $x_s$, the **alternating regret vector** $R_t\in\mathbb R^d$ is
--   $$
--   R_{t,i}=\sum_{s=1}^{t}(c_{s-1}+c_s)^\top x_s-\sum_{s=1}^{t}(c_{s-1,i}+c_{s,i}),\qquad i\in[d].
--   $$
--   Its $i$-th coordinate is the alternating regret against the pure action $e_i$. The potential argument of §2.2 is stated in terms of $R_t$.
--
--   **Formalization Note** $c_0=\mathbf 0$; for $t=0$ both sums are empty and $R_0=\mathbf 0$.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, §2.2, p.7

import Mathlib
import Definitions.Def_AltRegret_play

namespace AltRegret

/-- **The alternating regret vector `R_t`.** Tao–Zheng, arXiv:2608.24731, §2.2, p.7: "Define the
alternating regret vector `R_t` such that
`R_{t,i} = ∑_{s=1}^t (c_{s−1} + c_s)ᵀx_s − ∑_{s=1}^t (c_{s−1,i} + c_{s,i})` for all `i ∈ [d]`."

Here `x_s = play η β c s` is the play of the algorithm with parameters `(η, β)`.

**Formalization Note.** `c₀ = 0` via `lossAt`; for `t = 0` both sums are empty and `R₀ = 0`. -/
noncomputable def regretVector {d : ℕ} (η β : ℝ) (c : ℕ → Fin d → ℝ) (t : ℕ) : Fin d → ℝ :=
  fun i =>
    ∑ s ∈ Finset.Icc 1 t, ∑ j, (lossAt c (s - 1) j + lossAt c s j) * play η β c s j
      - ∑ s ∈ Finset.Icc 1 t, (lossAt c (s - 1) i + lossAt c s i)

end AltRegret


