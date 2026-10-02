-- Prove2me | Definitions.Def_MDPFinance_MeanVariance_TransactionCostMarket
-- name    : MDPFinance_MeanVariance_TransactionCostMarket
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:05:44.060021+00:00
-- url     : https://prove2.me/theorems/746bc5f3-20cf-47b1-b797-2b8ac8eaabc1
-- title:
--   The terminal-wealth Markov Decision Model with proportional transaction costs
-- statement:
--   State space $E := \mathbb{R}_{\ge0}^2$, a pair $(x_0,x_1)$ of bond and stock holdings
--   (after the previous transaction); the post-transaction stock holding $a\in[0,x_1+x_0/(1+c)]$ is
--   the action. Buying or selling stock to reach $a$ costs a proportion $c\in[0,1)$, paid from the
--   bond, giving the post-transaction bond holding
--   $$h(x_0,x_1,a) := \begin{cases} x_0+(1-c)(x_1-a) & 0\le a\le x_1 \\ x_0+(1+c)(x_1-a) & x_1 <
--   a \le x_1+\frac{x_0}{1+c}.\end{cases}$$
--   The transition is $T_n((x_0,x_1),a,z) := (h(x_0,x_1,a)(1+i_{n+1}), a\,z)$ for the relative stock
--   return $z=\tilde R_{n+1}$; there is no running reward, and the terminal reward is $g_N(x_0,x_1) :=
--   U(x_0+x_1)$ for a utility function $U$ that is strictly increasing, strictly concave, and
--   homogeneous of degree $\gamma$ on $[0,\infty)$.
--
--   This bundles the whole model of Bäuerle–Rieder §4.5: the market data (`TransactionCostMarket`),
--   the bond-holding-after-transaction map `h`, the admissible range `Arange`, and the abstract
--   homogeneity predicate `IsHomogeneousDeg` used by the value-function class `IsInIM` of the next
--   definition.
--
--   **Formalization Note.** Following the book's own reduction ("it is enough to determine the amount
--   invested in the stock after transaction"), the action is the single real number $a$ rather than a
--   pair, matching the book's practice for the rest of §4.5-4.6.
--
--   **Formalization Note (moderation).** The model carries Section 4.5's standing assumptions:
--   positive bond factors, independent price changes $\tilde R_n$, Assumption (FM)
--   (homogeneity, $\mathbb{E}\tilde R_n<\infty$), and $U$ a utility function (continuous as well
--   as strictly increasing and concave). `Estate` is the state space $E=\mathbb{R}^2_{\ge 0}$ and
--   `ratio` the stock-to-bond ratio in $[0,\infty]$ ($x_1/0=\infty$), so that the regions
--   $x_1/x_0 > q^+$, $x_1/x_0 < q^-$ read as the book intends (Lean's $x/0=0$ would put an all-stock
--   state into the hold region).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 107-108, PDF 121-122, model summary and unnumbered displays

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- The terminal-wealth Markov Decision Model with proportional transaction costs
(Bäuerle–Rieder, p. 106-107, PDF 120-121): state `(x0,x1) ∈ E := ℝ_{\ge0}²` (bond, stock
holdings), transition `T_n((x0,x1),a,z) := (h(x0,x1,a)(1+i_{n+1}), a z)` where `a ∈ [0, x1 +
x0/(1+c)]` is the stock holding *after* transaction and `h` (p. 108, PDF 122, unnumbered
display) accounts for the proportional cost `c ∈ [0,1)` paid from the bond; `r_n ≡ 0`,
`g_N(x0,x1) := U(x0+x1)` for a utility function `U` homogeneous of degree `γ`; the section's
standing Assumption (FM) (homogeneity, `𝔼 R̃_n < ∞`), independent price changes and positive bond
factors are fields. Reduced to the
scalar action `a` (the post-transaction stock holding) per the book's own reduction (p. 108, PDF
122: "it is enough to determine the amount invested in the stock after transaction"). -/
structure TransactionCostMarket (Ω : Type*) [MeasurableSpace Ω] where
  measIP : Measure Ω
  isProb : IsProbabilityMeasure measIP
  N : ℕ
  i : ℕ → ℝ
  hi_pos : ∀ n, 1 ≤ n → n ≤ N → 0 < 1 + i n
  c : ℝ
  hc0 : 0 ≤ c
  hc1 : c < 1
  Rtilde : ℕ → Ω → ℝ
  hRtilde_meas : ∀ n, 1 ≤ n → n ≤ N → Measurable (Rtilde n)
  hRtilde_pos : ∀ n, 1 ≤ n → n ≤ N → ∀ᵐ ω ∂measIP, 0 < Rtilde n ω
  /-- The relative price changes `R̃_1, …, R̃_N` are independent ("the independent disturbances"). -/
  hRtilde_indep : iIndepFun (fun n : Fin N => Rtilde (n.val + 1)) measIP
  /-- Assumption (FM)(ii): `𝔼‖R̃_n‖ < ∞`. -/
  hRtilde_int : ∀ n, 1 ≤ n → n ≤ N → Integrable (Rtilde n) measIP
  γ : ℝ
  /-- The utility function `U` (Definition 3.4.1, `dom U = [0,∞)`), homogeneous of degree `γ`
  (Assumption (FM)(i)). -/
  U : ℝ → ℝ
  hU_mono : StrictMonoOn U (Set.Ici 0)
  hU_concave : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) U
  hU_cont : ContinuousOn U (Set.Ici (0 : ℝ))
  hU_hom : ∀ x ≥ (0 : ℝ), ∀ lam > (0 : ℝ), U (lam * x) = lam ^ γ * U x

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `h(x,a)` (Bäuerle–Rieder, p. 108, PDF 122, unnumbered display), the bond holding after
buying/selling stock to reach post-transaction stock holding `a`, transaction costs paid from
the bond. -/
noncomputable def TransactionCostMarket.h (M : TransactionCostMarket Ω) (x0 x1 a : ℝ) : ℝ :=
  if a ≤ x1 then x0 + (1 - M.c) * (x1 - a) else x0 + (1 + M.c) * (x1 - a)

/-- The admissible post-transaction stock holdings, `0 ≤ a ≤ x1 + x0/(1+c)` (Bäuerle–Rieder,
p. 108, PDF 122). -/
def TransactionCostMarket.Arange (M : TransactionCostMarket Ω) (x0 x1 : ℝ) : Set ℝ :=
  Set.Icc 0 (x1 + x0 / (1 + M.c))

/-- The state space `E := ℝ_{\ge0}²` of bond and stock holdings. -/
def Estate : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2}

/-- A function `f : E → ℝ` is homogeneous of degree `γ` (Bäuerle–Rieder, p. 107, PDF 121):
`f(λx) = λ^γ f(x)` for `λ > 0` and `x ∈ E`. -/
def IsHomogeneousDeg (γ : ℝ) (f : ℝ × ℝ → ℝ) : Prop :=
  ∀ lam > (0 : ℝ), ∀ x ∈ Estate, f (lam * x.1, lam * x.2) = lam ^ γ * f x

/-- The stock-to-bond ratio `x1/x0 ∈ [0, ∞]` of a state `x ∈ E`, with `x1/0 = ∞` for `x1 > 0`
(and `0/0 := 0`), as the book's regions `x1/x0 > q^+`, `x1/x0 < q^-` read it. -/
noncomputable def ratio (x0 x1 : ℝ) : EReal :=
  if x0 = 0 then (if x1 = 0 then (0 : EReal) else ⊤) else ((x1 / x0 : ℝ) : EReal)

end MDPFinance.MeanVariance


