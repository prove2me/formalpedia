-- Prove2me | Definitions.Def_actuarial_aggregateMaximumClaim
-- name    : actuarial_aggregateMaximumClaim
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:24:51.763882+00:00
-- url     : https://prove2.me/theorems/3cb22ced-d88a-4391-9d24-086d1b8fde51
-- title:
--   Sum of maximum individual policy claims
-- statement:
--   Every policy has a fixed nonnegative integer benefit b(i). Adding benefits for the first n policies gives the maximum total loss attainable if they all claim, even when some individual benefits vanish.
--
--   **Mathematical statement**
--
--   $$
--   B_n=\sum_{i=0}^{n-1}b_i
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib

namespace ActuarialValuation

noncomputable def aggregateMaximumClaim (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, b i

end ActuarialValuation


