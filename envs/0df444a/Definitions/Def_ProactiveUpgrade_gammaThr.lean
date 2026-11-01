-- Prove2me | Definitions.Def_ProactiveUpgrade_gammaThr
-- name    : ProactiveUpgrade_gammaThr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:50:48.290975+00:00
-- url     : https://prove2.me/theorems/3a6b72a0-db2a-49fd-bcb0-405f96ac8bf5
-- title:
--   The threshold $\gamma_{i,t}(x_{-(i+1)})$
-- statement:
--   For $i=1,\dots,m-1$ and period $t$, with $x_{-(i+1)}$ the inventories of all products except $i+1$,
--
--   $$
--   \gamma_{i,t}(x_{-(i+1)})=\min\{x_{i+1}>0\mid \hat v_{t+1}(x-e_{i+1})\ge\hat v_{t+1}(x-e_i),\ x_i>0\}.
--   $$
--
--   It is the smallest stock of product $i+1$ at which, with product $i$ in stock, giving away a unit of $i+1$ is worth at least as much as selling a unit of $i$.
--
--   **Formalization Note** The minimum is the infimum in $\mathbb N\cup\{\infty\}$ (`ℕ∞`) over the values $k>0$ of coordinate $i+1$, the other coordinates of $x$ held fixed, so $\gamma$ does not depend on $x_{i+1}$. On an empty set it is $\infty$ (never offer), not the junk value $0$.
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, §6.1, p.24; Proof of Theorem 3, p.46

import Mathlib
import Definitions.Def_ProactiveUpgrade_vhat

namespace ProactiveUpgrade

/-- **The threshold `γ_{i,t}(x_{−(i+1)})`** (Chen et al., SSRN 3777846, §6.1, p.24; again in the
Proof of Theorem 3, p.46), for `i < m`:
`γ_{i,t}(x_{−(i+1)}) = min{x_{i+1} > 0 | v̂_{t+1}(x − e_{i+1}) ≥ v̂_{t+1}(x − eᵢ), xᵢ > 0}`.

**Formalization Note** The minimum is `sInf` in `ℕ∞` over the values `k > 0` of coordinate `i + 1`
(the other coordinates of `x` fixed), so it does not depend on `x_{i+1}`; the empty set gives `⊤`
(never offer), never the junk value `0`. -/
noncomputable def gammaThr {m : ℕ} (M : Model m) (T t : ℕ) (x : Fin m → ℕ) (i : Fin m)
    (h : i.val + 1 < m) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ k : ℕ, n = (k : ℕ∞) ∧ 0 < k ∧ 0 < x i ∧
    vhat M T (t + 1) (dec (Function.update x (succIdx i h) k) i) ≤
      vhat M T (t + 1) (dec (Function.update x (succIdx i h) k) (succIdx i h))}

end ProactiveUpgrade


