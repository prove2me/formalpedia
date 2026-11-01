-- Prove2me | Definitions.Def_PartPredAlloc_hyperPMF
-- name    : PartPredAlloc_hyperPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:15:40.215045+00:00
-- url     : https://prove2.me/theorems/fbc10505-25bd-4e7e-8ae5-ba4aee8d9f1c
-- title:
--   Hypergeometric probability mass function
-- statement:
--   When $d$ items are drawn without replacement from a population of $N$ items of which $m$ are defective, the number $K$ of defectives drawn satisfies
--
--   $$
--   \Pr(K=k)=\frac{\binom mk\binom{N-m}{d-k}}{\binom Nd},
--   $$
--
--   with mean $\mathbb E[K]=dm/N$. The paper writes $K\sim\mathrm{Hyper}(n_1,n,m)$ for $n_1$ draws from a population of $n$ items with $m$ defectives.
--
--   **Formalization Note** The population is `N`, the draws `d`, the defectives `m`, to avoid a clash with the model's $n$ and $n_1$.
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Theorem EC.2, p.ec2 (PDF 39)

import Mathlib

namespace PartPredAlloc

/-- The hypergeometric probability mass function (arXiv:1810.00447v1, Theorem EC.2, p.ec2 = PDF 39):
the probability that exactly `k` defectives are selected when `d` items are drawn without replacement
from a population of `N` items of which `m` are defective,
`P(K = k) = C(m, k) C(N − m, d − k) / C(N, d)`.

**Formalization Note.** The paper's `Hyper(n₁, n, m)` has `n₁` draws (here `d`), population `n`
(here `N`) and `m` defectives; other binder names avoid a clash with the model's `n, n₁`. The mean is
`d m / N`. Natural-number subtractions are used only with `m ≤ N` and `k ≤ d` in the theorems. -/
noncomputable def hyperPMF (N d m k : ℕ) : ℝ :=
  ((m.choose k : ℝ) * ((N - m).choose (d - k) : ℝ)) / (N.choose d : ℝ)

end PartPredAlloc


