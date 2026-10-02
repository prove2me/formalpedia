-- Prove2me | Definitions.Def_MDPFinance_TerminalWealth_Market
-- name    : MDPFinance_TerminalWealth_Market
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:54:01.596745+00:00
-- url     : https://prove2.me/theorems/f0aee35e-5d94-4f79-b71a-7fc8213088bf
-- title:
--   The multiperiod terminal wealth Markov Decision Model
-- statement:
--   The multiperiod terminal wealth model has state space $E := \mathrm{dom}\,U$ (wealth), action
--   space $\mathbb{R}^d$ (amounts invested in the risky assets), transition
--   $T_n(x,a,z) = (1+i_{n+1})(x+a\cdot z)$, $r_n \equiv 0$, $g_N := U$. $D_n(x) := \{a : (1+i_{n+1})(x+
--   a\cdot R_{n+1}) \in \mathrm{dom}\,U \text{ a.s.}\}$. The value $V_n^\pi(x) := \mathbb{E}[U(X_N)]$
--   of a Markov portfolio strategy $\pi$, and $V_n(x) := \sup_\pi V_n^\pi(x)$ over admissible $\pi$.
--
--   **Formalization Note.** $V$ is defined via an explicit sup over *admissible Markov portfolio
--   strategies* (not the Bellman recursion itself), so that the goal (Theorem 4.2.2) parts (b)/(c)
--   are genuine content, not restatements of this definition. The book's own Theorem 2.2.3
--   justifies restricting to Markov (rather than general history-dependent) strategies for this
--   model; this mission does not separately reprove that restriction.
--
--   **Formalization Note (moderation).** The model carries Section 4.2's standing assumptions:
--   positive bond factors, $R_1,\dots,R_N$ independent (without which the reduction to the Markov
--   Decision Model and the Bellman equation of Theorem 4.2.2 fail), and Assumption (FM)(i), no
--   arbitrage, in the local form of Theorem 3.1.5; Assumption (FM)(ii), $\mathbb{E}\|R_n\| <
--   \infty$, is `FM2`, carried by the theorems that use it (the exponential case does not).
--   Admissibility of a strategy is required at states $x \in E = \mathrm{dom}\,U$ only: at $x
--   \notin \mathrm{dom}\,U$ the set $D_n(x)$ is empty under no arbitrage, so requiring
--   admissibility there would leave no admissible strategy at all and make $V_n \equiv -\infty$.
--   $V_n^\pi$, $V_n$ are $[-\infty,\infty)$-valued as in the book.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 80-81, PDF 94-95, model summary and Eq. (4.4), (4.6)

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_OnePeriod

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- The multiperiod terminal wealth Markov Decision Model (Bäuerle–Rieder, p. 79-80, PDF 93-94):
state space `E := domU`, action space `A := ℝ^d`, transition `T_n(x,a,z) := (1+i_{n+1})(x+a·z)`,
`r_n ≡ 0`, `g_N := U`. Bundles the probability space, the interest rates (positive bond factors),
the relative risk process `R_1, …, R_N` of Section 3.1 — assumed independent, as at the start of
Section 4.2 — the standing no-arbitrage Assumption (FM)(i) (in its local form, Theorem 3.1.5),
and the utility function (Definition 3.4.1). -/
structure TerminalWealthMarket (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  measIP : Measure Ω
  isProb : IsProbabilityMeasure measIP
  N : ℕ
  i : ℕ → ℝ
  hi_pos : ∀ n, 1 ≤ n → n ≤ N → 0 < 1 + i n
  R : ℕ → Ω → (Fin d → ℝ)
  hR_meas : ∀ n, 1 ≤ n → n ≤ N → Measurable (R n)
  /-- `R_1, …, R_N` are independent (Section 4.2's standing assumption). -/
  hR_indep : iIndepFun (fun n : Fin N => R (n.val + 1)) measIP
  /-- Assumption (FM)(i): no arbitrage opportunities, in the local form of Theorem 3.1.5. -/
  hNA : ∀ n, 1 ≤ n → n ≤ N → NoArbitrageOnePeriod measIP (R n)
  domU : Set ℝ
  U : ℝ → ℝ
  hU_mono : StrictMonoOn U domU
  hU_concave : StrictConcaveOn ℝ domU U
  hU_cont : ContinuousOn U domU

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Assumption (FM)(ii) (Bäuerle–Rieder, p. 79, PDF 93): `𝔼‖R_n‖ < ∞` for `n = 1, …, N`. -/
def TerminalWealthMarket.FM2 (M : TerminalWealthMarket Ω d) : Prop :=
  ∀ n, 1 ≤ n → n ≤ M.N → Integrable (fun ω => ∑ k, |M.R n ω k|) M.measIP

/-- The bond price `S⁰_n := ∏_{k=1}^n (1+i_k)`, `S⁰_0 := 1` (Bäuerle–Rieder, p. 61, PDF 75). -/
noncomputable def TerminalWealthMarket.S0 (M : TerminalWealthMarket Ω d) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 + M.i (k + 1))

/-- The admissible actions `D_n(x)` (Bäuerle–Rieder, Eq. (4.4), p. 80, PDF 94):
`D_n(x) := {a ∈ ℝ^d | (1+i_{n+1})(x + a·R_{n+1}) ∈ domU  ℙ-a.s.}`. -/
def TerminalWealthMarket.D (M : TerminalWealthMarket Ω d) (n : ℕ) (x : ℝ) : Set (Fin d → ℝ) :=
  {a | ∀ᵐ ω ∂M.measIP, (1 + M.i (n + 1)) * (x + ∑ k, a k * M.R (n + 1) ω k) ∈ M.domU}

/-- A Markov portfolio strategy `π : ℕ → ℝ → (Fin d → ℝ)` is admissible over `[n,N)` if `π k` is
measurable and `π k x ∈ D_k(x)` for every stage `n ≤ k < N` and every state `x ∈ E = domU`
(Bäuerle–Rieder, p. 80, PDF 94: a policy of the Markov Decision Model with state space `domU`). -/
def TerminalWealthMarket.IsAdmissible (M : TerminalWealthMarket Ω d) (n : ℕ)
    (π : ℕ → ℝ → (Fin d → ℝ)) : Prop :=
  ∀ k, n ≤ k → k < M.N → (∀ x ∈ M.domU, π k x ∈ M.D k x) ∧ Measurable (π k)

/-- The terminal wealth `X_{n+k}` reached after `k` steps from time `n`, state `x`, under a
Markov portfolio strategy `π`, on the sample path `ω` (Bäuerle–Rieder, p. 80, PDF 94, transition
function `T_n(x,a,z) = (1+i_{n+1})(x+a·z)`, iterated). -/
def TerminalWealthMarket.terminalWealth (M : TerminalWealthMarket Ω d)
    (π : ℕ → ℝ → (Fin d → ℝ)) : (k : ℕ) → (n : ℕ) → (x : ℝ) → (ω : Ω) → ℝ
  | 0, _, x, _ => x
  | (k + 1), n, x, ω =>
      M.terminalWealth π k (n + 1)
        ((1 + M.i (n + 1)) * (x + ∑ j, π n x j * M.R (n + 1) ω j)) ω

/-- The value `V_n^π(x) := 𝔼[U(X_N)] ∈ [-∞, ∞)` of Markov portfolio strategy `π` from time `n`,
state `x` (Bäuerle–Rieder, Eq. (4.6), p. 80, PDF 94). -/
noncomputable def TerminalWealthMarket.Vpi (M : TerminalWealthMarket Ω d)
    (π : ℕ → ℝ → (Fin d → ℝ)) (n : ℕ) (x : ℝ) : EReal :=
  erealIntegral M.measIP (fun ω => (M.U (M.terminalWealth π (M.N - n) n x ω) : EReal))

/-- The value function `V_n(x) := sup_π V_n^π(x)`, the supremum over admissible Markov
portfolio strategies (Bäuerle–Rieder, Eq. (4.6), p. 80, PDF 94). -/
noncomputable def TerminalWealthMarket.V (M : TerminalWealthMarket Ω d) (n : ℕ) (x : ℝ) :
    EReal :=
  ⨆ π ∈ {π : ℕ → ℝ → (Fin d → ℝ) | M.IsAdmissible n π}, M.Vpi π n x

end MDPFinance.TerminalWealth


