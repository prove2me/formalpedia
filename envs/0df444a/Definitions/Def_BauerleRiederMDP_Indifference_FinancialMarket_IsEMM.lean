-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_FinancialMarket_IsEMM
-- name    : BauerleRiederMDP_Indifference_FinancialMarket_IsEMM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:56.508304+00:00
-- url     : https://prove2.me/theorems/f280320a-34ac-4876-a957-b210c9fcf056
-- title:
--   Equivalent martingale measures of the financial market
-- statement:
--   A probability measure $Q$ is an equivalent martingale measure if it has the same null sets as $\mathbb P$ and each discounted price process $(S^k_n/S^0_n)_{n=0,\dots,N}$ is an $(\mathcal F_n)$-martingale under $Q$.
--
--   **Formalization Note** Adaptedness comes with the market. The integrability and the one-step conditional expectations are written out for $n\le N$, because the martingale predicate of Mathlib ranges over the whole index type.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition C.1.1, p.365

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_FinancialMarket

open MeasureTheory

namespace BauerleRiederMDP.Indifference

namespace FinancialMarket

variable {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}

/-- An equivalent martingale measure (Bäuerle & Rieder, Markov Decision Processes with Applications
to Finance (2011), Definition C.1.1, p.365, PDF 370): a probability measure `Q` with the same null
sets as `ℙ` under which each discounted price process `(S^k_n/S⁰_n)`, `n = 0, …, N`, is an
`(𝓕_n)`-martingale.

**Formalization Note.** Adaptedness is `S_adapted` of the market. The martingale property is
written out for `n ≤ N` because Mathlib's `Martingale` ranges over the whole index type. `Q` is a
measure on `(Ω, 𝓕)`, as in Definition C.1.1 a). -/
def IsEMM (M : FinancialMarket Ω d N) (Q : Measure Ω) : Prop :=
  IsProbabilityMeasure Q ∧ Q ≪ M.P ∧ M.P ≪ Q ∧ ∀ k,
    (∀ n, n ≤ N → Integrable (fun ω => M.S n ω k / M.S0 n) Q) ∧
    ∀ n, n < N → Q[fun ω => M.S (n + 1) ω k / M.S0 (n + 1) | M.F n] =ᵐ[Q]
      fun ω => M.S n ω k / M.S0 n

end FinancialMarket

end BauerleRiederMDP.Indifference


