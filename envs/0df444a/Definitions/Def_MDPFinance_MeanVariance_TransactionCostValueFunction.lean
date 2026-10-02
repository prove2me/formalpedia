-- Prove2me | Definitions.Def_MDPFinance_MeanVariance_TransactionCostValueFunction
-- name    : MDPFinance_MeanVariance_TransactionCostValueFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:06:42.98309+00:00
-- url     : https://prove2.me/theorems/226aab8a-71c7-4b9c-8f84-c67626079619
-- title:
--   Admissible Markov strategies and the value function of the transaction-cost model
-- statement:
--   A Markov strategy $\pi:\mathbb{N}\to\mathbb{R}^2\to\mathbb{R}$ (the post-transaction
--   stock holding, as a function of the current $(x_0,x_1)$) is admissible over $[n,N)$
--   (`IsAdmissible`) if $\pi_k(x_0,x_1)\in\mathrm{Arange}(x_0,x_1)$ and $\pi_k$ is measurable for
--   every $n\le k<N$. `terminalState` recurses the wealth pair forward under $\pi$; the value of a
--   fixed strategy is $V_n^\pi(x_0,x_1) := \mathbb{E}[U(X^0_N+X^1_N)]$ (`Vpi`), and the value
--   function is
--   $$V_n(x_0,x_1) := \sup_{\pi \text{ admissible on } [n,N)} V_n^\pi(x_0,x_1).$$
--
--   **Formalization Note.** `terminalState` mirrors the recursive `terminalWealth` pattern used
--   throughout this book's missions (e.g. chunk `04a`'s `TerminalWealthMarket`), specialized to the
--   two-coordinate $(x_0,x_1)$ state of the transaction-cost model.
--
--   **Formalization Note (moderation).** Admissibility is required at states of $E$ only;
--   requiring $\pi_k(x)\in\mathrm{Arange}(x)$ at states with negative coordinates (where the range
--   is empty) would leave no admissible strategy and make $V_n\equiv 0$ (the real supremum of the
--   empty set).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 107-108, PDF 121-122, unnumbered displays

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A Markov policy sequence `π : ℕ → ℝ × ℝ → ℝ` (post-transaction stock holding, as a function
of `(x0,x1)`) is admissible over `[n,N)` if `π k (x0,x1) ∈ Arange x0 x1` for every `n ≤ k < N`
and every state `(x0,x1) ∈ E = ℝ_{\ge0}²`, and `π k` is measurable. -/
def TransactionCostMarket.IsAdmissible (M : TransactionCostMarket Ω) (n : ℕ)
    (π : ℕ → ℝ × ℝ → ℝ) : Prop :=
  ∀ k, n ≤ k → k < M.N → (∀ x ∈ Estate, π k x ∈ M.Arange x.1 x.2) ∧ Measurable (π k)

/-- The terminal holdings `(X⁰,X¹)` reached after `k` steps from time `n`, state `(x0,x1)`,
under `π`, on path `ω`. -/
noncomputable def TransactionCostMarket.terminalState (M : TransactionCostMarket Ω)
    (π : ℕ → ℝ × ℝ → ℝ) :
    (k : ℕ) → (n : ℕ) → (x0 x1 : ℝ) → (ω : Ω) → ℝ × ℝ
  | 0, _, x0, x1, _ => (x0, x1)
  | (k + 1), n, x0, x1, ω =>
      let a := π n (x0, x1)
      M.terminalState π k (n + 1) (M.h x0 x1 a * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω) ω

/-- The value `V_n^π(x0,x1) := 𝔼[U(X⁰_N+X¹_N)]` of Markov strategy `π` from time `n`, state
`(x0,x1)`. -/
noncomputable def TransactionCostMarket.Vpi (M : TransactionCostMarket Ω) (π : ℕ → ℝ × ℝ → ℝ)
    (n : ℕ) (x0 x1 : ℝ) : ℝ :=
  ∫ ω, (fun p => M.U (p.1 + p.2)) (M.terminalState π (M.N - n) n x0 x1 ω) ∂M.measIP

/-- The value function `V_n(x0,x1) := sup_π V_n^π(x0,x1)` over admissible Markov strategies. -/
noncomputable def TransactionCostMarket.V (M : TransactionCostMarket Ω) (n : ℕ) (x0 x1 : ℝ) :
    ℝ :=
  ⨆ π ∈ {π : ℕ → ℝ × ℝ → ℝ | M.IsAdmissible n π}, M.Vpi π n x0 x1

end MDPFinance.MeanVariance


