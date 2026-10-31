-- Prove2me | Definitions.Def_OceanPlastic_CaseO
-- name    : OceanPlastic_CaseO
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:34.428997+00:00
-- url     : https://prove2.me/theorems/5277c9cf-2fd2-4b55-9137-e189c857c4b5
-- title:
--   Case O: processor objective (2), outcomes (3), firm profit, impacts and the TBL objective $T^O$
-- statement:
--   In Case O the firm pays bonuses $r_c$ to collectors and $r_p$ to the processor per unit of recycled plastic, and sells $d_o$ plastic offsets. Given the bonuses, the processor maximizes
--   $$(p_m-h+r_p)\,q_t(h+r_c)\quad\text{over } h\ge0. \tag{2}$$
--
--   With total bonus $r=r_c+r_p$, the paper's outcomes are
--   $$\Pi^O_C(r)=\Pi^O_P(r)=\frac{M(p_m+r)^2}{4k},\qquad V^O(r)=\frac{M(p_m+r)}{2k}. \tag{3}$$
--
--   The firm's profit, social impact and environmental impact are
--   $$\Pi^O_F(r,d_o)=\Bigl(\bar v_o+\delta_o r-\frac{\bar v_o}{Q_o}d_o\Bigr)d_o-r\,V^O(r),$$
--   $$S^O(r)=\bigl(\Pi^O_C(r)-\Pi^B_C\bigr)+\rho_p\bigl(\Pi^O_P(r)-\Pi^B_P\bigr),\qquad E^O(r)=c_E^r\bigl(V^O(r)-V^B\bigr),$$
--   and its triple-bottom-line objective with weights $\rho_1,\rho_2,\rho_3$ is
--   $$T^O(d_o,r)=\rho_1\Pi^O_F(r,d_o)+\rho_2 S^O(r)+\rho_3E^O(r).$$
--
--   These are the objective and the two impact measures compared throughout the mission.
--
--   **Formalization Note** The module declares `processorObjO`, `VO`, `PiOC`, `PiOP`, `PiOF`, `SO`, `EO`, `TO` in the namespace `OceanPlastic.Params`. The closed forms (3) are definitions, as the paper uses them in problem (4); the milestone `eq_3` says when they are the lower stages' equilibrium.
-- source:
--   Baron–Romero–Zhang–Zhou, Innovative Business Models in Ocean-Bound Plastic Recycling, MSOM, doi:10.1287/msom.2022.0643, §3.2(a), pp.10–11, eq. (2), (3)

import Mathlib
import Definitions.Def_OceanPlastic_Params
import Definitions.Def_OceanPlastic_Benchmark

namespace OceanPlastic

namespace Params

/-- **The processor's objective in Case O** given bonuses `r_c`, `r_p`: the objective
`(p_m − h + r_p) q_t(h + r_c)` of problem (2). Baron–Romero–Zhang–Zhou, MSOM,
doi:10.1287/msom.2022.0643, §3.2(a), eq. (2), p. 10. -/
noncomputable def processorObjO (P : Params) (rc rp h : ℝ) : ℝ :=
  (P.pm - h + rp) * P.qt (h + rc)

/-- **Recycled volume in Case O** at total bonus `r`: `V^O(r) = M (p_m + r) / (2k)`,
eq. (3), p. 10. -/
noncomputable def VO (P : Params) (r : ℝ) : ℝ :=
  P.M * (P.pm + r) / (2 * P.k)

/-- **Collectors' total income in Case O** at total bonus `r`:
`Π^O_C(r) = M (p_m + r)² / (4k)`, eq. (3), p. 10 (gross payment received). -/
noncomputable def PiOC (P : Params) (r : ℝ) : ℝ :=
  P.M * (P.pm + r) ^ 2 / (4 * P.k)

/-- **Processor's profit in Case O** at total bonus `r`:
`Π^O_P(r) = M (p_m + r)² / (4k)`, eq. (3), p. 10. -/
noncomputable def PiOP (P : Params) (r : ℝ) : ℝ :=
  P.M * (P.pm + r) ^ 2 / (4 * P.k)

/-- **The firm's profit in Case O**:
`Π^O_F(r, d_o) = (v̄_o + δ_o r − (v̄_o / Q_o) d_o) d_o − r V^O(r)`, p. 10. -/
noncomputable def PiOF (P : Params) (r d : ℝ) : ℝ :=
  (P.vbar + P.δ * r - P.vbar / P.Q * d) * d - r * P.VO r

/-- **The firm's social impact in Case O**:
`S^O(r) = (Π^O_C(r) − Π^B_C) + ρ_p (Π^O_P(r) − Π^B_P)`, p. 10. -/
noncomputable def SO (P : Params) (r : ℝ) : ℝ :=
  (P.PiOC r - P.PiBC) + P.ρp * (P.PiOP r - P.PiBP)

/-- **The firm's environmental impact in Case O**: `E^O(r) = c_E^r (V^O(r) − V^B)`, p. 10. -/
noncomputable def EO (P : Params) (r : ℝ) : ℝ :=
  P.cE * (P.VO r - P.VB)

/-- **The firm's triple-bottom-line objective in Case O**:
`T^O(d_o, r) = ρ₁ Π^O_F(r, d_o) + ρ₂ S^O(r) + ρ₃ E^O(r)`, p. 11. -/
noncomputable def TO (P : Params) (ρ₁ ρ₂ ρ₃ d r : ℝ) : ℝ :=
  ρ₁ * P.PiOF r d + ρ₂ * P.SO r + ρ₃ * P.EO r

end Params

end OceanPlastic


