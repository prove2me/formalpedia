-- Prove2me | Definitions.Def_AnalystRanking_Revelation_expPostVar
-- name    : AnalystRanking_Revelation_expPostVar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:36:29.30399+00:00
-- url     : https://prove2.me/theorems/fcf3fee0-ace6-4e46-902f-88274cf99d12
-- title:
--   Expected posterior variance $\mathbb E[\mathrm{Var}(\omega\mid m_i,m_j)]$
-- statement:
--   With $H=1$, $L=0$ (p. 24), for each forecast pair $m=(m_i,m_j)$,
--   $$\Pr(m)\,\mathrm{Var}(\omega\mid m)=\Pr(m)\Pr(H\mid m)\Pr(L\mid m)=\frac{\Pr(H,m)\Pr(L,m)}{\Pr(H,m)+\Pr(L,m)},$$
--   with $\Pr(H,m)=q\Pr(m\mid H)$, $\Pr(L,m)=(1-q)\Pr(m\mid L)$. The expected posterior variance is the sum of these terms over the four forecast pairs; it is the denominator of (6).
--
--   **Formalization Note** A forecast pair of probability zero contributes $0$ (Lean's $x/0=0$), which is its true contribution. Under the standing assumptions the sum is positive.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Definition 3, display (6), p. 24; (B.45), p. 53

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_fcastJoint

namespace AnalystRanking.Revelation

/-- **Expected posterior variance `𝔼_{m_i, m_j}[Var(ω | m_i, m_j)]`.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Definition 3, display (6), p. 24, with "`H = 1` and `L = 0` such that `𝔼[ω] = q` and
`Var(ω) = q(1 − q)`"; see (B.45), p. 53.

For each forecast pair `m`, `Pr(m) Var(ω | m) = Pr(m) Pr(H|m) Pr(L|m) = Pr(H, m) Pr(L, m) / Pr(m)`;
`expPostVar q γ ρ σ` is the sum of these over the four pairs.

**Formalization Note.** A pair with `Pr(m) = 0` contributes `0` through Lean's `x / 0 = 0`, which
is its true contribution. With `0 < q < 1`, `1/2 < γ < 1`, `ρ ∈ [0, 1]` and `σ ∈ [0, 1]²` the sum
is positive. -/
noncomputable def expPostVar (q γ ρ : ℝ) (σ : ℝ × ℝ) : ℝ :=
  ∑ mi : Bool, ∑ mj : Bool,
    (q * fcastJoint γ ρ σ true mi mj) * ((1 - q) * fcastJoint γ ρ σ false mi mj) /
      (q * fcastJoint γ ρ σ true mi mj + (1 - q) * fcastJoint γ ρ σ false mi mj)

end AnalystRanking.Revelation


