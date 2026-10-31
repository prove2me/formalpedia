-- Prove2me | Definitions.Def_OceanPlastic_Params
-- name    : OceanPlastic_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:13.883407+00:00
-- url     : https://prove2.me/theorems/88bf86b6-62f5-4fc0-a497-ab469ed3f239
-- title:
--   Parameters of the ocean-bound plastic recycling model
-- statement:
--   A local supply chain consists of $M$ plastic collectors and one processor, who sells recycled plastic in the local market at the exogenous price $p_m$. Collecting $q$ units costs a collector $kq^2/2$, where $k$ is the labour intensity. A firm may enter and sell plastic offsets to a market of potential size $Q_o$, whose customers have environmental values uniform on $[0,\bar v_o]$ and a perceived social value $\delta_o$ per unit of bonus. In the firm's social impact the processor's profit increase has weight $\rho_p$, and $c_E^r$ is the environmental value of recycling one unit of regular plastic.
--
--   The parameters satisfy
--   $$M,\ k,\ \bar v_o,\ Q_o>0,\qquad \delta_o\in[0,1),\qquad p_m\ge 0,\qquad \rho_p\in(0,1],\qquad c_E^r\ge 0.$$
--
--   These are the standing assumptions of every statement in this mission.
--
--   **Formalization Note** The ranges of $k$, $\delta_o$, $\rho_p$ are printed in the paper. The ranges of the other parameters are readings: sizes and the upper end of a uniform law are positive, a price is non-negative, and the paper gives no sign for $c_E^r$. The ranges are fields of the structure `Params`, so that every statement about a `P : Params` assumes them.
-- source:
--   Baron–Romero–Zhang–Zhou, Innovative Business Models in Ocean-Bound Plastic Recycling, MSOM, doi:10.1287/msom.2022.0643, §3.1–3.2(a), pp.7–11; Table 1, p.33

import Mathlib

namespace OceanPlastic

/-- **Parameters of the ocean-bound plastic recycling model (Benchmark and Case O).**
Baron–Romero–Zhang–Zhou, *Innovative Business Models in Ocean-Bound Plastic Recycling*, MSOM,
doi:10.1287/msom.2022.0643, §3.1–3.2(a), pp. 7–11; Table 1, p. 33.

* `M`: number of collectors (`M > 0`);
* `k`: labour intensity of collecting plastic ("k > 0", p. 8); collecting `q` units costs
  a collector `k q² / 2`;
* `vbar`: upper end `v̄_o` of the customers' environmental value `v_o ∼ U(0, v̄_o)`, p. 10;
* `Q`: potential market size `Q_o` for plastic offsets;
* `δ`: social value per unit of bonus, `δ_o ∈ [0, 1)`, p. 10;
* `pm`: price `p_m` of recycled plastic in the local market;
* `ρp`: weight `ρ_p ∈ (0, 1]` of the processor's profit increase in the social impact, p. 11;
* `cE`: environmental value `c_E^r` of recycling one unit of regular plastic.

**Formalization Note** The ranges of `k`, `δ`, `ρp` are printed in the paper. The readings
`M, vbar, Q > 0` (sizes and the upper end of a uniform law), `pm ≥ 0` (a price) and `cE ≥ 0`
(the paper gives no sign) are ours. `M` is a real number, as the paper treats it (it
differentiates in `M`). The ranges are fields of the structure, so that every `P : Params`
satisfies them and every theorem about `P` assumes them. -/
structure Params where
  /-- number of collectors `M` -/
  M : ℝ
  /-- labour intensity `k` -/
  k : ℝ
  /-- upper end `v̄_o` of the customers' environmental value -/
  vbar : ℝ
  /-- potential market size `Q_o` for plastic offsets -/
  Q : ℝ
  /-- social value per unit of bonus `δ_o` -/
  δ : ℝ
  /-- local market price `p_m` of recycled plastic -/
  pm : ℝ
  /-- weight `ρ_p` of the processor's profit increase in the social impact -/
  ρp : ℝ
  /-- environmental value `c_E^r` of recycling one unit of regular plastic -/
  cE : ℝ
  M_pos : 0 < M
  k_pos : 0 < k
  vbar_pos : 0 < vbar
  Q_pos : 0 < Q
  δ_nonneg : 0 ≤ δ
  δ_lt_one : δ < 1
  pm_nonneg : 0 ≤ pm
  ρp_pos : 0 < ρp
  ρp_le_one : ρp ≤ 1
  cE_nonneg : 0 ≤ cE

end OceanPlastic


