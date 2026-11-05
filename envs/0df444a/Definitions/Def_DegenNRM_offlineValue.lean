-- Prove2me | Definitions.Def_DegenNRM_offlineValue
-- name    : DegenNRM_offlineValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:41.315567+00:00
-- url     : https://prove2.me/theorems/ff80e1b1-7d3a-4422-88fe-ebbb910fdb5e
-- title:
--   The prophet's value $V^{\mathrm{off}}(I)$, problem (2)
-- statement:
--   For capacities $C\in\mathbb R^m$ and a sample path $I$ of $T$ periods (period $t$ has type $j_t$, size $\tilde a_t=a_{j_t}$ and reward $\tilde r_t$), the offline optimum is
--   $$V^{\mathrm{off}}(I)=\max\Big\{\sum_{t=1}^T\tilde r_t x_t\;:\;\sum_{t=1}^T\tilde a_{t,i}x_t\le C_i\ \forall i\in[m],\ x\in\{0,1\}^T\Big\}.$$
--   It is the value of the prophet, who knows the whole sample path, and the benchmark of the regret (3).
--
--   **Formalization Note** The maximum is the supremum of a finite set; for $C\ge0$ the set is nonempty ($x=0$ is feasible), so the supremum is the maximum.
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, §2, (2), p.6

import Mathlib
import Definitions.Def_DegenNRM_Instance

namespace DegenNRM

/-- **The prophet's value `V^off(I)`, problem (2)** (Jiang, Ma & Zhang, arXiv:2210.07996v5,
§2, (2), p.6).

For capacities `C` and a sample path `ω` of `T` periods (period `t` carries the type `(ω t).1`
and the reward `(ω t).2`),
`V^off(I) = max Σ_t r̃_t x_t  s.t.  Σ_t ã_{t,i} x_t ≤ C_i ∀ i,  x_t ∈ {0, 1}`.

**Formalization Note.** A decision `x ∈ {0,1}^T` is `x : Fin T → Bool`. The maximum is the
`sSup` of the finitely many feasible values; for `C ≥ 0` the set is nonempty (`x = 0` is
feasible), so this `sSup` is the maximum of (2). -/
noncomputable def offlineValue {m n T : ℕ} (inst : Instance m n) (C : Fin m → ℝ)
    (ω : Fin T → Fin n × ℝ) : ℝ :=
  sSup ((fun x : Fin T → Bool => ∑ t, if x t then (ω t).2 else 0) ''
    {x | ∀ i, (∑ t, if x t then inst.a (ω t).1 i else 0) ≤ C i})

end DegenNRM


