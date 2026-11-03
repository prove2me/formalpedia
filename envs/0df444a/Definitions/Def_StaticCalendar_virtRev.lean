-- Prove2me | Definitions.Def_StaticCalendar_virtRev
-- name    : StaticCalendar_virtRev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:27:45.911204+00:00
-- url     : https://prove2.me/theorems/eb72240a-b713-451a-89bb-8539f5cf4f12
-- title:
--   Expected revenue of the virtual calendar $J_{\mathsf C}$
-- statement:
--   The expected revenue $J_{\mathsf C}(c,t)$ of the **virtual calendar**, with $k=T-t+1$ periods left and inventories $c$. In every period each item $i$ is offered at the virtual price $p_{\mathsf C,i}$, its demand has the mixture law of item $i$, demands are independent across periods, and sales are truncated by the remaining inventory.
--
--   **Formalization Note** The paper fixes the per-item laws only. Demands are taken independent across items here; any coupling gives the same value, because the revenue is a sum of one-item revenues.
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Step 0, pp.ec10–ec11

import Mathlib
import Definitions.Def_StaticCalendar_nuItem
import Definitions.Def_StaticCalendar_pC

open MeasureTheory

namespace StaticCalendar

/-- The revenue of `k` periods of the virtual calendar from inventories `c`, when `X t i` is the
demand for item `i` in period `t`: item `i` always sells at the price `pc i` and sells
`min{Bᵢ, X t i}`, arXiv:1811.01077v5, pp.ec10–ec11. -/
def virtPathRev {n : ℕ} (pc : Fin n → ℝ) :
    (k : ℕ) → (Fin n → ℝ) → (Fin k → Fin n → ℝ) → ℝ
  | 0, _, _ => 0
  | k + 1, c, X => ∑ i, pc i * min (c i) (X 0 i) +
      virtPathRev pc k (fun i => c i - min (c i) (X 0 i)) (Fin.tail X)

/-- `J_C(c,t)`, arXiv:1811.01077v5, pp.ec10–ec11 (with `k = T - t + 1`): the expected revenue of
always offering the deterministic assortment `S_C = {(i, p_{C,i})}` under static substitution from
inventories `c`.

**Formalization Note.** Demands are independent across periods, and each period's demand for
item `i` has law `nuItem I x i`. The paper fixes only these marginals; the demands are taken
independent across items, and any coupling gives the same value because the revenue is a sum of
one-item revenues. -/
noncomputable def virtRev {n m : ℕ} (I : DemandModel n m) (x : Assortment n m → ℝ)
    (c : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∫ X, virtPathRev (pC I x) k c X
    ∂(Measure.pi fun _ : Fin k => Measure.pi fun i : Fin n => nuItem I x i)

end StaticCalendar


