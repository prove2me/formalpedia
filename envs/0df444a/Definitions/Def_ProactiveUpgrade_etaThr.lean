-- Prove2me | Definitions.Def_ProactiveUpgrade_etaThr
-- name    : ProactiveUpgrade_etaThr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:50:37.352546+00:00
-- url     : https://prove2.me/theorems/18f18893-8d25-4757-a9e2-3b053002aea3
-- title:
--   The threshold $\eta_{i,t}(x_{-(i+1)})$
-- statement:
--   For $i=1,\dots,m-1$ and period $t$,
--
--   $$
--   \eta_{i,t}(x_{-(i+1)})=\min\{x_{i+1}>0\mid \hat v_{t+1}(x-e_{i+1})+p_i\ge\hat v_{t+1}(x),\ x_i=0\}.
--   $$
--
--   It is the smallest stock of product $i+1$ at which, with product $i$ out of stock, selling a unit of $i+1$ at price $p_i$ is worth at least as much as keeping it.
--
--   **Formalization Note** As for $\gamma$: the infimum in `ℕ∞` over the values $k>0$ of coordinate $i+1$, independent of $x_{i+1}$, and $\infty$ on an empty set.
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, §6.1, p.24; Proof of Theorem 3, p.46

import Mathlib
import Definitions.Def_ProactiveUpgrade_vhat

namespace ProactiveUpgrade

/-- **The threshold `η_{i,t}(x_{−(i+1)})`** (Chen et al., SSRN 3777846, §6.1, p.24; again in the
Proof of Theorem 3, p.46), for `i < m`:
`η_{i,t}(x_{−(i+1)}) = min{x_{i+1} > 0 | v̂_{t+1}(x − e_{i+1}) + pᵢ ≥ v̂_{t+1}(x), xᵢ = 0}`.

**Formalization Note** The minimum is `sInf` in `ℕ∞` over the values `k > 0` of coordinate `i + 1`
(the other coordinates of `x` fixed), so it does not depend on `x_{i+1}`; the empty set gives `⊤`
(never offer). -/
noncomputable def etaThr {m : ℕ} (M : Model m) (T t : ℕ) (x : Fin m → ℕ) (i : Fin m)
    (h : i.val + 1 < m) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ k : ℕ, n = (k : ℕ∞) ∧ 0 < k ∧ x i = 0 ∧
    vhat M T (t + 1) (Function.update x (succIdx i h) k) ≤
      vhat M T (t + 1) (dec (Function.update x (succIdx i h) k) (succIdx i h)) + M.p i}

end ProactiveUpgrade


