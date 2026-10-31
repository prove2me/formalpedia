-- Prove2me | Definitions.Def_PrideGuilt_Standing
-- name    : PrideGuilt_Standing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:41.885561+00:00
-- url     : https://prove2.me/theorems/b5fd1221-eefc-4b9d-b05a-fedc2e8bb253
-- title:
--   Standing assumptions of the pride–guilt model
-- statement:
--   The parameters $(b_0,b_1,c_n,c_u,c_e,I_P,I_G,\tau^0)$ satisfy the paper's standing assumptions when
--
--   $$
--   b_0>0,\qquad b_0\ge b_1\ge 0,\qquad c_n>c_u,\qquad I_P\ge0,\qquad I_G\ge0,\qquad \tau^0\in[0,1],\qquad 1-b_1I_G-b_0c_n\ge0 .
--   $$
--
--   The intrinsic utilities are introduced on p.7 ("$I_P\ge0$ ($-I_G\le0$)"), the initial proportion $\tau^0\in[0,1]$ in Lemma 1 (p.9), the demand and cost assumptions on p.11, and the last inequality on p.12, where it guarantees a feasible and profitable market in the benchmark without remanufacturing.
--
--   **Formalization Note** The assumptions on the pride and guilt parameters ($\gamma_P>0$, $\gamma_G>0$ on p.7 and $\gamma_P\ne\gamma_G$ on p.9) are hypotheses of each theorem, since $\gamma_P,\gamma_G$ are arguments rather than parameters. The recycling cost $c_e$ carries no sign assumption, as in the paper.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), p.7 (I_P ≥ 0, −I_G ≤ 0); Lemma 1, p.9 (τ^0 ∈ [0,1]); p.11 (b_0 > 0, b_0 ≥ b_1 ≥ 0, c_n > c_u); p.12 (1 − b_1I_G − b_0c_n ≥ 0)

import Mathlib
import Definitions.Def_PrideGuilt_Params

namespace PrideGuilt

/-- **The paper's standing assumptions on the parameters.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721:
p.7 (PDF 8) `I_P ≥ 0` and `−I_G ≤ 0`; p.9 (PDF 10) `τ⁰ ∈ [0, 1]`;
p.11 (PDF 12) `b₀ > 0`, `b₀ ≥ b₁ ≥ 0`, `c_n > c_u`; p.12 (PDF 13) `1 − b₁I_G − b₀c_n ≥ 0`.

The assumptions on pride and guilt (`γ_P > 0`, `γ_G > 0` on p.7 and `γ_P ≠ γ_G` on p.9) are
stated as separate hypotheses of each theorem, because `γ_P` and `γ_G` are arguments, not
parameters. The recycling cost `c_e` has no sign assumption in the paper and none here. -/
structure Standing (P : Params) : Prop where
  b0_pos : 0 < P.b0
  b1_nonneg : 0 ≤ P.b1
  b1_le_b0 : P.b1 ≤ P.b0
  cu_lt_cn : P.cu < P.cn
  IP_nonneg : 0 ≤ P.IP
  IG_nonneg : 0 ≤ P.IG
  τ0_nonneg : 0 ≤ P.τ0
  τ0_le_one : P.τ0 ≤ 1
  market : 0 ≤ 1 - P.b1 * P.IG - P.b0 * P.cn

end PrideGuilt


