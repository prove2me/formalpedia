-- Prove2me | Definitions.Def_MDPFinance_ConsumptionInvestment_Market
-- name    : MDPFinance_ConsumptionInvestment_Market
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:59:31.852579+00:00
-- url     : https://prove2.me/theorems/a567066b-5c97-4a3d-8a13-81e5e39bca13
-- title:
--   The multiperiod consumption-investment Markov Decision Model
-- statement:
--   State space $E := \mathrm{dom}\,U_p$ (wealth), action space $\mathbb{R}_{\ge0} \times
--   \mathbb{R}^d$ (consumption $c$, amounts $a$ invested), transition
--   $T_n(x,c,a,z) := (1+i_{n+1})(x-c+a\cdot z)$, $r_n(x,c,a) := U_c(c)$, $g_N := U_p$.
--   $D_n(x) := \{(c,a) : 0 \le c \le x,\ (1+i_{n+1})(x-c+a\cdot R_{n+1}) \in \mathrm{dom}\,U_p
--   \text{ a.s.}\}$. $V_n^\pi(x) := \mathbb{E}[\sum_{k=n}^{N-1} U_c(c_k(X_k)) + U_p(X_N)]$,
--   $V_n(x) := \sup_\pi V_n^\pi(x)$ over admissible Markov strategies.
--
--   **Formalization Note.** Analogous to chunk `04a`'s `TerminalWealthMarket`, with the action space
--   extended to a joint $(c,a)$ pair and the running consumption reward accumulated alongside the
--   terminal utility, matching the book's own reduction "using the same arguments as in Section 4.2
--   for the terminal wealth problem."**
--
--   **Formalization Note (moderation).** The model carries Section 4.3's standing assumptions:
--   positive bond factors, $R_1,\dots,R_N$ independent, Assumption (FM)(i) (no arbitrage, local
--   form); (FM)(ii), $\mathbb{E}\|R_n\|<\infty$, is `FM2`, a hypothesis of the theorems. The
--   consumption $c$ lies in the domain of $U_c$ (for $\log$, $c > 0$; Lean's $\log 0 = 0$ would
--   otherwise let $c = 0$ masquerade as a finite-utility choice), admissibility is required at
--   states $x \in E = \mathrm{dom}\,U$ only, and $V_n^\pi$, $V_n$ are $[-\infty,\infty)$-valued.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 94, PDF 108-109, model summary and unnumbered displays

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_OnePeriod

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- The multiperiod consumption-investment Markov Decision Model (Bäuerle–Rieder, p. 93-94, PDF
107-108): state space `E := domU` (wealth; `dom U_c = dom U_p = domU`), action space
`A := ℝ_{\ge0} × ℝ^d` (consumption `c`, amounts `a` invested in the risky assets), transition
`T_n(x,c,a,z) := (1+i_{n+1})(x-c+a\cdot z)`, `r_n(x,c,a) := U_c(c)`, `g_N := U_p`. The market is
that of Section 4.2: positive bond factors, independent relative risks `R_1, …, R_N`, and
Assumption (FM)(i), no arbitrage (local form, Theorem 3.1.5). -/
structure ConsumptionInvestmentMarket (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  measIP : Measure Ω
  isProb : IsProbabilityMeasure measIP
  N : ℕ
  i : ℕ → ℝ
  hi_pos : ∀ n, 1 ≤ n → n ≤ N → 0 < 1 + i n
  R : ℕ → Ω → (Fin d → ℝ)
  hR_meas : ∀ n, 1 ≤ n → n ≤ N → Measurable (R n)
  hR_indep : iIndepFun (fun n : Fin N => R (n.val + 1)) measIP
  hNA : ∀ n, 1 ≤ n → n ≤ N → NoArbitrageOnePeriodCI measIP (R n)
  domU : Set ℝ
  Uc : ℝ → ℝ
  Up : ℝ → ℝ
  hUc_mono : StrictMonoOn Uc domU
  hUc_concave : StrictConcaveOn ℝ domU Uc
  hUc_cont : ContinuousOn Uc domU
  hUp_mono : StrictMonoOn Up domU
  hUp_concave : StrictConcaveOn ℝ domU Up
  hUp_cont : ContinuousOn Up domU

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Assumption (FM)(ii) (Bäuerle–Rieder, p. 79, PDF 93): `𝔼‖R_n‖ < ∞` for `n = 1, …, N`. -/
def ConsumptionInvestmentMarket.FM2 (M : ConsumptionInvestmentMarket Ω d) : Prop :=
  ∀ n, 1 ≤ n → n ≤ M.N → Integrable (fun ω => ∑ k, |M.R n ω k|) M.measIP

/-- The bond price `S⁰_n := ∏_{k=1}^n (1+i_k)`. -/
noncomputable def ConsumptionInvestmentMarket.S0 (M : ConsumptionInvestmentMarket Ω d) (n : ℕ) :
    ℝ :=
  ∏ k ∈ Finset.range n, (1 + M.i (k + 1))

/-- The admissible actions `D_n(x) := {(c,a) | 0 ≤ c ≤ x, c ∈ dom U_c,
(1+i_{n+1})(x-c+a\cdot R_{n+1}) ∈ domU ℙ-a.s.}` (Bäuerle–Rieder, p. 94, PDF 108). -/
def ConsumptionInvestmentMarket.D (M : ConsumptionInvestmentMarket Ω d) (n : ℕ) (x : ℝ) :
    Set (ℝ × (Fin d → ℝ)) :=
  {ca | 0 ≤ ca.1 ∧ ca.1 ≤ x ∧ ca.1 ∈ M.domU ∧
    ∀ᵐ ω ∂M.measIP, (1 + M.i (n + 1)) * (x - ca.1 + ∑ k, ca.2 k * M.R (n + 1) ω k) ∈ M.domU}

/-- A Markov consumption-investment strategy `π : ℕ → ℝ → ℝ × (Fin d → ℝ)` is admissible over
`[n,N)` if `π k` is measurable and `π k x ∈ D_k(x)` for every `n ≤ k < N` and every state
`x ∈ E = domU`. -/
def ConsumptionInvestmentMarket.IsAdmissible (M : ConsumptionInvestmentMarket Ω d) (n : ℕ)
    (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) : Prop :=
  ∀ k, n ≤ k → k < M.N → (∀ x ∈ M.domU, π k x ∈ M.D k x) ∧ Measurable (π k)

/-- The terminal state `X_{n+k}` and the accumulated consumption reward, reached after `k`
steps from time `n`, state `x`, under `π`, on path `ω`. -/
def ConsumptionInvestmentMarket.stateAcc (M : ConsumptionInvestmentMarket Ω d)
    (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) : (k : ℕ) → (n : ℕ) → (x : ℝ) → (ω : Ω) → ℝ × ℝ
  | 0, _, x, _ => (x, 0)
  | (k + 1), n, x, ω =>
      let c := (π n x).1
      let a := (π n x).2
      let rest := M.stateAcc π k (n + 1)
        ((1 + M.i (n + 1)) * (x - c + ∑ j, a j * M.R (n + 1) ω j)) ω
      (rest.1, M.Uc c + rest.2)

/-- The value `V_n^π(x) := 𝔼[Σ_{k=n}^{N-1} U_c(c_k(X_k)) + U_p(X_N)] ∈ [-∞, ∞)` of Markov
strategy `π` from time `n`, state `x` (Bäuerle–Rieder, p. 94, PDF 108, unnumbered display). -/
noncomputable def ConsumptionInvestmentMarket.Vpi (M : ConsumptionInvestmentMarket Ω d)
    (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (n : ℕ) (x : ℝ) : EReal :=
  erealIntegral M.measIP
    (fun ω => (((M.stateAcc π (M.N - n) n x ω).2 + M.Up (M.stateAcc π (M.N - n) n x ω).1 : ℝ) :
      EReal))

/-- The value function `V_n(x) := sup_π V_n^π(x)` over admissible Markov strategies
(Bäuerle–Rieder, p. 94, PDF 108). -/
noncomputable def ConsumptionInvestmentMarket.V (M : ConsumptionInvestmentMarket Ω d) (n : ℕ)
    (x : ℝ) : EReal :=
  ⨆ π ∈ {π : ℕ → ℝ → ℝ × (Fin d → ℝ) | M.IsAdmissible n π}, M.Vpi π n x

end MDPFinance.ConsumptionInvestment


