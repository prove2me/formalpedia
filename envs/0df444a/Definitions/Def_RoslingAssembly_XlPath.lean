-- Prove2me | Definitions.Def_RoslingAssembly_XlPath
-- name    : RoslingAssembly_XlPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:36:53.151769+00:00
-- url     : https://prove2.me/theorems/3d8dd39e-587c-468f-b091-98ce27f2e5c9
-- title:
--   Echelon stock on hand after arrivals $X^l_{kt}$
-- statement:
--   $X^l_{kt}$ is the **echelon inventory of item $k$ on hand** in period $t$ after the arrivals of that period and before ordering:
--   $$X^l_{kt}=Y_{k,t-l_k}-\sum_{s=t-l_k}^{t-1}\xi_s ,$$
--   with the convention that an empty sum is $0$; so $X^l_{kt}=Y_{kt}$ when $l_k=0$. An assembly of item $i$ can only use components $k\in P(i)$ that are on hand: $Y_{it}\le X^l_{kt}$.
--
--   **Formalization Note** The sum $\sum_{s=a}^{b}$ is over `Finset.Ico a (b+1)`, empty when $a>b$. Periods are integers; periods $\le0$ use the pre-horizon history.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, pp. 566–567, Problem P

import Mathlib
import Definitions.Def_RoslingAssembly_Ypath
import Definitions.Def_RoslingAssembly_demPath

namespace RoslingAssembly

/-- **Echelon inventory on hand after arrivals**, X^l_kt (§1, pp. 566–567). Rosling, *Optimal
Inventory Policies for Assembly Systems under Random Demands*, Operations Research 37(4), 1989,
p. 566: "X^l_it = echelon inventory on hand of item i in period t before ordering decisions are
made but after assembles arrive = Y_{i,t−l_i} − Σ_{k=t−l_i}^{t−1} ξ_k. (Throughout this paper, it
is assumed that a sum, Σ_a^b, equals zero if a > b.)"; p. 567, Problem P:
"X^l_kt = Y_{k,t−l_k} − Σ_{s=t−l_k}^{t−1} ξ_s".

`XlPath ℓ Yh ξh pol ω t k = Y_{k,t−l_k} − Σ_{s=t−l_k}^{t−1} ξ_s` along the demand path `ω`, with
lead times `ℓ`.

**Formalization Note.** Periods are integers with the paper's numbering; the sum Σ_{s=a}^{b} is
`Finset.Ico a (b + 1)`, which is empty when `a > b` (the paper's convention), so `l_k = 0` gives
`X^l_kt = Y_kt`. Periods `≤ 0` use the pre-horizon history. -/
noncomputable def XlPath {N : ℕ} (ℓ : Fin N → ℕ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ)
    (pol : ℕ → (ℕ → ℝ) → Fin N → ℝ) (ω : ℕ → ℝ) (t : ℤ) (k : Fin N) : ℝ :=
  Ypath Yh pol ω (t - ℓ k) k - ∑ s ∈ Finset.Ico (t - ℓ k) t, demPath ξh ω s

end RoslingAssembly


