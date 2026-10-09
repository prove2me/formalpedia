-- Prove2me | Definitions.Def_actuarial_aggregateBernoulliPMF
-- name    : actuarial_aggregateBernoulliPMF
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:24:22.064879+00:00
-- url     : https://prove2.me/theorems/82f7220b-79cb-4ff4-a99c-ddd73ee890f4
-- title:
--   Bernoulli insurance claim of a fixed integer amount
-- statement:
--   A single policy pays either no claim with mass one minus p or an integer claim b with mass p. When b=0, these two event contributions coincide at payment zero and the probability mass there correctly becomes one.
--
--   **Mathematical statement**
--
--   $$
--   h_{p,b}(s)=(1-p)\mathbf1_{\{s=0\}}+p\mathbf1_{\{s=b\}}
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib

namespace ActuarialValuation

noncomputable def aggregateBernoulliPMF (p : ℝ) (b s : ℕ) : ℝ :=
  (if s = 0 then 1 - p else 0) + (if s = b then p else 0)

end ActuarialValuation


