-- Prove2me | Definitions.Def_actuarial_aggregatePortfolioPMF
-- name    : actuarial_aggregatePortfolioPMF
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:25:23.791765+00:00
-- url     : https://prove2.me/theorems/7a376e65-c187-4a62-a16c-0dfcb4487c38
-- title:
--   Recursive aggregate distribution for independent Bernoulli policies
-- statement:
--   The zero-policy portfolio has probability one of no loss. Each further policy is introduced by convolving the existing aggregate-loss mass with its independent Bernoulli claim law. Policy i may have its own probability and integer claim amount, so homogeneity is not assumed.
--
--   **Mathematical statement**
--
--   $$
--   g_0=\delta_0,\quad g_{n+1}=g_n*h_{p_n,b_n}
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution
import Definitions.Def_actuarial_aggregateBernoulliPMF

namespace ActuarialValuation

noncomputable def aggregatePortfolioPMF (p : ℕ → ℝ) (b : ℕ → ℕ) :
    ℕ → ℕ → ℝ
  | 0 => fun s => if s = 0 then 1 else 0
  | n + 1 => fun s =>
      aggregateConvolution
        (aggregatePortfolioPMF p b n)
        (aggregateBernoulliPMF (p n) (b n)) s

end ActuarialValuation


