-- Prove2me | Definitions.Def_IntADSat_binomGE
-- name    : IntADSat_binomGE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:22.199204+00:00
-- url     : https://prove2.me/theorems/7770fde9-a90f-4a64-889a-e646936ef5c4
-- title:
--   Binomial upper tail $\Pr[\mathrm{Bin}(N,1/2)\ge j]$
-- statement:
--   For $N\in\mathbb N$ and an integer $j$, with $\mathrm{Bin}(N,1/2)$ the number of heads in $N$ fair coin flips,
--
--   $$
--   \Pr[\mathrm{Bin}(N,1/2)\ge j]=\sum_{0\le i\le N,\ i\ge j}\binom Ni2^{-N},
--   $$
--
--   for every integer $j$ (it is $1$ for $j\le 0$ and $0$ for $j>N$). These are the binomial tails in Lemmas B.3 and B.4 (degrees in $G(n,1/2)$ are $\mathrm{Bin}(n-1,1/2)$).
--
--   **Formalization Note** The point masses are the published binomial probability `QuasiPolyTrace.bin N i (1/2)`$=\binom Ni2^{-N}$, which is also used directly for the point probabilities $\Pr[\mathrm{Bin}(N,1/2)=j]$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemmas B.3 and B.4, pp.15–16 (PDF 16–17)

import Mathlib
import Definitions.Def_QuasiPolyTrace_bin

set_option autoImplicit false

namespace IntADSat

/-- The upper tail `Pr[Bin(N, 1/2) ≥ j]` at an integer `j`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemmas B.3 and B.4, pp.15–16 (PDF 16–17)): `∑_{0 ≤ i ≤ N, i ≥ j} C(N, i)/2^N`.

**Formalization Note** The point masses are the published binomial probability
`QuasiPolyTrace.bin N i (1/2) = C(N, i) (1/2)^i (1/2)^(N−i)`. -/
noncomputable def binomGE (N : ℕ) (j : ℤ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), if j ≤ (i : ℤ) then QuasiPolyTrace.bin N i (1 / 2) else 0

end IntADSat


