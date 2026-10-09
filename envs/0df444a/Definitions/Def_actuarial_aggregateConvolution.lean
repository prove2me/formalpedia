-- Prove2me | Definitions.Def_actuarial_aggregateConvolution
-- name    : actuarial_aggregateConvolution
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:24:10.424248+00:00
-- url     : https://prove2.me/theorems/48eb4b32-b294-4ae4-941f-4b6f55a513b5
-- title:
--   Discrete convolution of two aggregate-claim distributions
-- statement:
--   At aggregate claim amount s, the joint probability coefficient is a sum over every possible split k and s-k between two independent portfolios. Indexing the split from zero through s avoids negative claim amounts and makes this definition purely a finite real sum.
--
--   **Mathematical statement**
--
--   $$
--   (f*g)(s)=\sum_{k=0}^{s}f(k)g(s-k)
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib

namespace ActuarialValuation

noncomputable def aggregateConvolution (f g : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (s + 1), f k * g (s - k)

end ActuarialValuation


