-- Prove2me | Definitions.Def_AnalystRanking_Revelation_IsCompEq
-- name    : AnalystRanking_Revelation_IsCompEq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:34:32.948481+00:00
-- url     : https://prove2.me/theorems/98a4b276-4f66-4498-9f4c-2771579afb40
-- title:
--   Symmetric equilibrium under competition, Definition 1
-- statement:
--   A symmetric strategy $\sigma=(\sigma^h,\sigma^l)$ is an **equilibrium under competition** when $\sigma\in[0,1]^2$, $\sigma^h\ge1-\sigma^l$, and each signal type plays a best response against every mixed deviation: for every $\tau\in[0,1]$,
--   $$\tau U(\hat h\mid h)+(1-\tau)U(\hat l\mid h)\le \sigma^hU(\hat h\mid h)+(1-\sigma^h)U(\hat l\mid h),$$
--   $$\tau U(\hat l\mid l)+(1-\tau)U(\hat h\mid l)\le \sigma^lU(\hat l\mid l)+(1-\sigma^l)U(\hat h\mid l).
--   Here $U$ is the interim rank payoff when the other analyst also plays $\sigma$, with Bayes beliefs.
--
--   This is Definition 1 (p. 9) for the symmetric profile $\sigma_i=\sigma_j=\sigma$, together with the paper's restriction "without loss of generality … $\sigma^h\geqslant1-\sigma^l$" (cases violating it are relabelings of $h$ and $l$). These are the equilibria among which Definition 2 selects the most informative one.
--
--   **Formalization Note** The set $\mathcal E$ of Definition 2 is read as the set of symmetric equilibria obeying the p. 9 restriction.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Definition 1, display (5), and the restriction σh ⩾ 1 − σl, p. 9

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_interimPay

namespace AnalystRanking.Revelation

/-- **Symmetric equilibrium under analyst competition, Definition 1.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Definition 1, display (5), p. 9: a strategy profile in which, "for each `s_i ∈ S_i`",
analyst `i` maximizes `𝔼_{ω, m_j}[u_i(m_i(σ_i), m_j(σ_j*), ω) | s_i]` with beliefs consistent with
Bayes' rule; "I consider a symmetric equilibrium such that `σ_i = σ_j = σ` … Also, without loss of
generality, I restrict attention to `σʰ ⩾ 1 − σˡ`" (p. 9).

`IsCompEq w1 w0 w2 q γ ρ σ` holds when `σ ∈ [0, 1]²`, `1 − σˡ ≤ σʰ`, and, with
`U = interimPay w1 w0 w2 q γ ρ σ` (the other analyst plays `σ`), for every `τ ∈ [0, 1]` the high-signal type's mixed payoff `τ U(ĥ|h) + (1 − τ) U(l̂|h)` is at most
`σʰ U(ĥ|h) + (1 − σʰ) U(l̂|h)`, and the low-signal type's `τ U(l̂|l) + (1 − τ) U(ĥ|l)` is at most
`σˡ U(l̂|l) + (1 − σˡ) U(ĥ|l)`.

**Formalization Note.** Reading: the set `ℰ` of Definition 2 is the set of symmetric equilibria
satisfying the p. 9 restriction `σʰ ≥ 1 − σˡ`. Best responses are checked against every mixed
deviation, separately for each signal type. -/
def IsCompEq (w1 w0 w2 q γ ρ : ℝ) (σ : ℝ × ℝ) : Prop :=
  0 ≤ σ.1 ∧ σ.1 ≤ 1 ∧ 0 ≤ σ.2 ∧ σ.2 ≤ 1 ∧ 1 - σ.2 ≤ σ.1 ∧
  (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
    τ * interimPay w1 w0 w2 q γ ρ σ true true + (1 - τ) * interimPay w1 w0 w2 q γ ρ σ true false ≤
      σ.1 * interimPay w1 w0 w2 q γ ρ σ true true +
        (1 - σ.1) * interimPay w1 w0 w2 q γ ρ σ true false) ∧
  (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
    τ * interimPay w1 w0 w2 q γ ρ σ false false + (1 - τ) * interimPay w1 w0 w2 q γ ρ σ false true ≤
      σ.2 * interimPay w1 w0 w2 q γ ρ σ false false +
        (1 - σ.2) * interimPay w1 w0 w2 q γ ρ σ false true)

end AnalystRanking.Revelation


