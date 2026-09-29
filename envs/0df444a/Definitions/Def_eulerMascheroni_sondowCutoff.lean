-- Prove2me | Definitions.Def_eulerMascheroni_sondowCutoff
-- name    : eulerMascheroni_sondowCutoff
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:53:00.527336+00:00
-- url     : https://prove2.me/theorems/dd585389-a283-47e7-b0b5-40f1a2be0a3a
-- title:
--   Sondow cutoff remainder and finite-shift correction
-- statement:
--   Write $K_n(x,y)=[x(1-x)y(1-y)]^n/((1-xy)(-\log(xy)))$. Define
--   $$R_{n,N}=\int_0^1\int_0^1 K_n(x,y)(xy)^N\,dy\,dx,$$
--   $$E_{n,N}=\sum_{i=0}^n\binom ni^2(H_{N+n+i}-H_N)
--   +2\sum_{0\le i<j\le n}\frac{(-1)^{i+j}\binom ni\binom nj}{j-i}
--   \sum_{k=1}^{j-i}\log\left(1+\frac{n+i+k}{N}\right).$$
--   The remainder comes from truncating the geometric series. The correction collects finite shifts after extracting $H_N-\log N$. The finite evaluation uses $n,N>0$; no theorem is asserted by these definitions.
-- source:
--   J. Sondow, https://arxiv.org/pdf/math/0209070, v2 (2002). Equation (9), p. 7; finite evaluation and asymptotic rearrangement, pp. 8-9.

import Definitions.Def_eulerMascheroni_sondow

noncomputable section
namespace EulerMascheroni.Sondow
open Finset

def remainder (n N : ℕ) : ℝ :=
  ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
    ((x*(1-x)*y*(1-y))^n / ((1-x*y)*(-Real.log (x*y)))) * (x*y)^N

-- The finite-shift terms in the evaluation of I_n - R_{n,N}.
def cutoffError (n N : ℕ) : ℝ :=
  (∑ i ∈ range (n+1), (n.choose i : ℝ)^2 *
    ((harmonic (N+n+i) : ℝ) - (harmonic N : ℝ))) +
  2 * ∑ i ∈ range (n+1), ∑ j ∈ Icc (i+1) n,
    ((-1:ℝ)^(i+j)*(n.choose i : ℝ)*(n.choose j : ℝ)/(j-i:ℕ)) *
      ∑ k ∈ Icc 1 (j-i), Real.log (1+(n+i+k:ℕ)/(N:ℝ))

end EulerMascheroni.Sondow


