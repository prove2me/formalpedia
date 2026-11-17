-- Prove2me | Definitions.Def_Max3CutHard_Supplement_rho
-- name    : Max3CutHard_Supplement_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:47:14.480264+00:00
-- url     : https://prove2.me/theorems/f883cbda-f92e-46df-8f04-6b71d997e864
-- title:
--   The ratio $\rho$ of the soundness criterion
-- statement:
--   Let $(I_0,I_1,I_2)$ be a family of gadgets for Max-$k$-Cut, $k\ge3$, with completeness values $C_t=\min\{V_t(x,y^\circ):x\in\mathrm{sat}_t\}$. The **ratio of the soundness criterion** is
--
--   $$\rho=\frac{\max_{x\in[k]^3}\max_{y}S_y(x)}{\sum_{t\in\mathbb Z_3}C_t}.$$
--
--   Theorem 4.1 shows that the family yields NP-hardness of approximating Max-$k$-Cut within $\rho+\delta$ for every $\delta>0$, and Theorem 7.1 shows $\rho\ge27/29$ for every Max-3-Cut family.
--
--   The paper maximises over $y\in Y_k$; this equals the maximum over all $y\in[k]^k$ (Section 2, p.5), which is what the definition uses.
--
--   **Formalization Note** $C_t$ is the published `Max3CutHard.Ct` (it takes the proof of $3\le k$). The quotient is meaningful only when $\sum_tC_t>0$; Lean's division gives $0$ otherwise, so every theorem using $\rho$ assumes $\sum_tC_t>0$.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Theorem 4.1, p.7

import Mathlib
import Definitions.Def_Max3CutHard_Family
import Definitions.Def_Max3CutHard_Ct
import Definitions.Def_Max3CutHard_Supplement_maxS

namespace Max3CutHard.Supplement

open Max3CutHard

/-- **The ratio `ρ` of the soundness criterion.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Theorem 4.1, p.7:
"Let `ρ = max_{y∈Y_k} max_{x∈[k]^3} S_y(x) / Σ_{t∈Z3} C_t`."

**Formalization Note.** The numerator is `maxS F`, the maximum over all `x` and all
`y : Fin k → Fin k` (equal to the paper's maximum over `y ∈ Y_k`, p.5). `C_t` is the published
`Ct hk F t` (with `3 ≤ k`). `ρ` is meaningful only when `Σ_t C_t > 0`; at `Σ_t C_t = 0` Lean's
division returns `0`, so every statement that uses `rho` carries the hypothesis
`0 < Σ_t C_t`. -/
noncomputable def rho {k : ℕ} [NeZero k] (hk : 3 ≤ k) (F : Family k) : ℝ :=
  maxS F / ∑ t : ZMod 3, Ct hk F t

end Max3CutHard.Supplement


