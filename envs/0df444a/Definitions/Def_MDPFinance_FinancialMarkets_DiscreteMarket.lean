-- Prove2me | Definitions.Def_MDPFinance_FinancialMarkets_DiscreteMarket
-- name    : MDPFinance_FinancialMarkets_DiscreteMarket
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:47:19.312659+00:00
-- url     : https://prove2.me/theorems/ef505606-4154-4997-a0be-0dc8c4100b6e
-- title:
--   An $N$-period financial market and its relative risk process
-- statement:
--   An **$N$-period financial market** with $d$ risky assets consists of a probability space
--   $(\Omega,\mathcal{F},\mathbb{P})$ with filtration $(\mathcal{F}_n)$, $\mathcal{F}_0$ trivial;
--   a riskless bond with deterministic per-period rate $i_n$ (so $S^0_n = S^0_{n-1}(1+i_n)$); and
--   $d$ risky assets whose relative price changes $\tilde R_n = (\tilde R^1_n,\dots,\tilde
--   R^d_n)$ are $\mathcal{F}_n$-measurable and a.s. strictly positive ($S^k_n = S^k_{n-1}\tilde
--   R^k_n$). The **relative risk process** is $R_n^k := \tilde R_n^k/(1+i_n) - 1$.
--
--   **Formalization Note.** The market's own price processes $S^0, S^k$ are not represented as
--   separate fields (they would just be the running products of `i`/`Rtilde`, never referenced
--   again once `R` is available); `i` and `Rtilde` are the primitives Theorem 3.1.5 and the
--   wealth recursion actually need.
--
--   **Formalization Note (moderation).** The bond factors $1+i_n$ are required to be positive
--   ($S^0_n > 0$), which the relative risk process $R_n = \tilde R_n/(1+i_n) - 1$ and the wealth
--   recursion (3.1) presuppose; with $1 + i_n = 0$ the field's division would be Lean's $x/0 = 0$
--   and Theorem 3.1.5 would fail. Adaptedness and positivity of $\tilde R_n$ are required for
--   $n = 1,\dots,N$, the indices the model uses.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 61-63, PDF 75-77, §3.1 introduction (unnumbered displays)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.FinancialMarkets

/-- An `N`-period financial market with `d` risky assets and one riskless bond
(Bäuerle–Rieder, p. 61, PDF 75-76): a probability space `(Ω,𝓕,ℙ)` with filtration `(Fam n)`,
`Fam 0` trivial; a deterministic per-period interest rate `i : ℕ → ℝ` (`i (n+1)` the rate on
`[n,n+1)`); and relative price changes `R̃ : ℕ → Ω → Fin d → ℝ` (`R̃ (n+1)` the vector of
relative returns on `[n,n+1)`, `Fam (n+1)`-measurable, a.s. strictly positive, for
`n = 0, …, N-1`); the bond factors `1 + i_n` are positive. -/
structure DiscreteFinancialMarket (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  measIP : Measure Ω
  isProb : IsProbabilityMeasure measIP
  N : ℕ
  Fam : ℕ → MeasurableSpace Ω
  hFam_mono : Monotone Fam
  hFam_le : ∀ n, Fam n ≤ ‹MeasurableSpace Ω›
  hFam0_trivial : ∀ s, MeasurableSet[Fam 0] s → s = ∅ ∨ s = Set.univ
  i : ℕ → ℝ
  /-- The bond price `S⁰_{n+1} = S⁰_n (1 + i_{n+1})` stays positive, so that the relative risk
  process `R̃/(1+i) − 1` and the wealth recursion (3.1) are meaningful. -/
  hi_pos : ∀ n, 1 ≤ n → n ≤ N → 0 < 1 + i n
  Rtilde : ℕ → Ω → (Fin d → ℝ)
  hRtilde_adapted : ∀ n, 1 ≤ n → n ≤ N → @Measurable Ω (Fin d → ℝ) (Fam n) _ (Rtilde n)
  hRtilde_pos : ∀ n, 1 ≤ n → n ≤ N → ∀ᵐ ω ∂measIP, ∀ k, 0 < Rtilde n ω k

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The relative risk process `R_n^k := R̃_n^k / (1 + i_n) - 1` (Bäuerle–Rieder, p. 63, PDF 77,
unnumbered display) — the excess return of asset `k` over the riskless rate, on `[n-1,n)`. -/
noncomputable def DiscreteFinancialMarket.R (M : DiscreteFinancialMarket Ω d) (n : ℕ) (ω : Ω)
    (k : Fin d) : ℝ :=
  M.Rtilde n ω k / (1 + M.i n) - 1

end MDPFinance.FinancialMarkets


