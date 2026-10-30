-- Prove2me | Definitions.Def_AnalystRanking_Revelation_IsBenchEq
-- name    : AnalystRanking_Revelation_IsBenchEq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:35:09.744886+00:00
-- url     : https://prove2.me/theorems/8814f17d-e5da-4206-b562-09eecef78efe
-- title:
--   Symmetric equilibrium in the benchmark
-- statement:
--   A symmetric strategy $\sigma=(\sigma^h,\sigma^l)$ is a **benchmark equilibrium** when $\sigma\in[0,1]^2$, $\sigma^h\ge1-\sigma^l$, and each signal type plays a best response against every mixed deviation: for every $\tau\in[0,1]$,
--   $$\tau U(\hat h\mid h)+(1-\tau)U(\hat l\mid h)\le \sigma^hU(\hat h\mid h)+(1-\sigma^h)U(\hat l\mid h),$$
--   $$\tau U(\hat l\mid l)+(1-\tau)U(\hat h\mid l)\le \sigma^lU(\hat l\mid l)+(1-\sigma^l)U(\hat h\mid l).
--   Here $U$ is the benchmark payoff $W\Pr(\text{forecast correct}\mid s)$ of §3.1.
--
--   This is the benchmark of §3.1 (p. 10), where analysts care only about their own accuracy, with the solution concept and the restriction of p. 9.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §3.1, p. 10; Definition 1 and the restriction σh ⩾ 1 − σl, p. 9

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_benchPay

namespace AnalystRanking.Revelation

/-- **Symmetric equilibrium in the benchmark without ranking, §3.1 with Definition 1.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §3.1, p. 10 ("each analyst maximizes his own forecast accuracy without any concern about his
ranking"; objective `max_σ 𝔼_ω[u_i(m_i(σ_i), ω) | s_i]`), with the symmetric-equilibrium
convention and the restriction `σʰ ⩾ 1 − σˡ` of p. 9.

`IsBenchEq W q γ σ` holds when `σ ∈ [0, 1]²`, `1 − σˡ ≤ σʰ`, and, with `U = benchPay W q γ`,
for every `τ ∈ [0, 1]` the high-signal type's mixed payoff `τ U(ĥ|h) + (1 − τ) U(l̂|h)` is at most
`σʰ U(ĥ|h) + (1 − σʰ) U(l̂|h)`, and the low-signal type's `τ U(l̂|l) + (1 − τ) U(ĥ|l)` is at most
`σˡ U(l̂|l) + (1 − σˡ) U(ĥ|l)`.

**Formalization Note.** Same shape as `IsCompEq`, with the accuracy payoff `π_a = W`, `π_na = 0`;
the benchmark payoff does not depend on the other analyst. -/
def IsBenchEq (W q γ : ℝ) (σ : ℝ × ℝ) : Prop :=
  0 ≤ σ.1 ∧ σ.1 ≤ 1 ∧ 0 ≤ σ.2 ∧ σ.2 ≤ 1 ∧ 1 - σ.2 ≤ σ.1 ∧
  (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
    τ * benchPay W q γ true true + (1 - τ) * benchPay W q γ true false ≤
      σ.1 * benchPay W q γ true true + (1 - σ.1) * benchPay W q γ true false) ∧
  (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
    τ * benchPay W q γ false false + (1 - τ) * benchPay W q γ false true ≤
      σ.2 * benchPay W q γ false false + (1 - σ.2) * benchPay W q γ false true)

end AnalystRanking.Revelation


