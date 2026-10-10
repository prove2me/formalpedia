-- Prove2me | Definitions.Def_PriceQualityService_Surplus_ConsumerSurplus
-- name    : PriceQualityService_Surplus_ConsumerSurplus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:38.779492+00:00
-- url     : https://prove2.me/theorems/e58ee6f0-5fbc-4064-aed1-c609b803446c
-- title:
--   MNL consumer surplus $\log(1+\sum_i \exp(\alpha_i q_i - p_i + t_i s_i))$
-- statement:
--   In the setting of the MNL choice model with prices $\mathbf p$, qualities $\mathbf q$ and service durations $\mathbf t$, the **consumer surplus** is
--   $$
--   \mathrm{CS}(\mathbf p,\mathbf q,\mathbf t)=\log\Big(1+\sum_{i\in\mathcal N}\exp(\alpha_iq_i-p_i+t_is_i)\Big).
--   $$
--   By Anderson, de Palma and Thisse (1992) this is the expected maximal utility $E[\max_{i\in\mathcal N^+}U_i]$ of a consumer when the random parts of the utilities are i.i.d. Gumbel, with the outside option $0$ included in $\mathcal N^+=\mathcal N\cup\{0\}$.
--
--   Consumer surplus is the welfare measure of Proposition 5, which compares it across the firm's decision problems.
--
--   **Formalization Note** The expected-maximum identity is cited, not formalized: the log-sum formula is the definition.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 1 (PDF p. 34), proof of Proposition 5

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model

namespace PriceQualityService.Surplus

open Finset

/-- Consumer surplus under the MNL model (Wang, Ke & Cui, accepted manuscript (SSRN 3766191),
Online Supplement p. 1, proof of Proposition 5, citing Anderson et al. 1992):
`CS(p, q, t) = log(1 + ∑_{i ∈ 𝒩} exp(α_i q_i − p_i + t_i s_i))`.
The identity `E[max_{i ∈ 𝒩⁺} U_i] = CS` under i.i.d. Gumbel shocks is cited, not formalized:
the log-sum formula is the definition. -/
noncomputable def consumerSurplus {N : ℕ} (α s : Fin N → ℝ) (p q t : Fin N → ℝ) : ℝ :=
  Real.log (1 + ∑ i, PriceQualityService.Joint.attraction α s p q t i)

end PriceQualityService.Surplus


