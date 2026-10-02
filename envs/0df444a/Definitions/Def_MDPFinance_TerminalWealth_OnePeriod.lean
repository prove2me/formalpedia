-- Prove2me | Definitions.Def_MDPFinance_TerminalWealth_OnePeriod
-- name    : MDPFinance_TerminalWealth_OnePeriod
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:52:49.278777+00:00
-- url     : https://prove2.me/theorems/96171101-bb70-4b2a-9363-879d7fe2100d
-- title:
--   The one-period optimization problem $D(x)$, $u(x,a)$, $v(x)$
-- statement:
--   For a one-period market with utility $U$, interest rate $i$ and relative risk $R$: the
--   admissible investments are $D(x) := \{a \in \mathbb{R}^d : (1+i)(x+a\cdot R) \in \mathrm{dom}\,U
--   \text{ a.s.}\}$; $u(x,a) := \mathbb{E}[U((1+i)(x+a\cdot R))]$; $v(x) := \sup_{a \in D(x)} u(x,a)$.
--   A market with relative risk $R$ has **no arbitrage** if no $a$ has $a\cdot R \geq 0$ a.s. and
--   $\mathbb{P}(a\cdot R>0)>0$.
--
--   **Formalization Note.** This is the generic *one-period* market (a single $i$, $R$, no time
--   index), matching §4.1's own notational convention, independent of the $N$-period model of
--   `TerminalWealthMarket`.
--
--   **Formalization Note (moderation).** $u(x,a)$ and $v(x)$ take values in $[-\infty,\infty)$
--   (the extended-real integral of chunk `02a`): an expected utility that is $-\infty$ (possible
--   for $U = \log$) is recorded as $-\infty$, not as a default real value that a real-valued
--   Bochner integral would return and that could exceed the true supremum.
--   `StrictConcaveOnEReal` is strict concavity for such functions.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 91, PDF 91, Eq. (4.1)-(4.2) and unnumbered displays

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- The integral `∫ v dμ ∈ [-∞,∞)` of an extended-real-valued function `v` that never equals
`⊤` (restated from `MDPFinance.Bellman.erealIntegral`, chunk `02a`): the Lebesgue integrals of the
positive and negative parts are combined with `EReal`'s total addition (`⊤ + (-⊤) = ⊥`), so an
expected utility that is `-∞` is recorded as `-∞`, never as a default real value. -/
noncomputable def erealIntegral {E : Type*} [MeasurableSpace E] (μ : Measure E) (v : E → EReal) :
    EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

/-- `f` is strictly concave on `s ⊆ ℝ`, for an `EReal`-valued `f` (Mathlib's `StrictConcaveOn`
needs a module structure on the codomain, which `EReal` lacks): `s` is convex and
`a f(x) + b f(y) < f(a x + b y)` for distinct `x, y ∈ s` and `a, b > 0`, `a + b = 1`. -/
def StrictConcaveOnEReal (s : Set ℝ) (f : ℝ → EReal) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
    (a : EReal) * f x + (b : EReal) * f y < f (a * x + b * y)

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The one-period market's admissible actions (Bäuerle–Rieder, p. 77, PDF 91, unnumbered
display): `D(x) := {a ∈ ℝ^d | (1+i)(x + a·R) ∈ domU ℙ-a.s.}`. -/
def OnePeriodD (measIP : Measure Ω) (domU : Set ℝ) (i : ℝ) (R : Ω → Fin d → ℝ) (x : ℝ) :
    Set (Fin d → ℝ) :=
  {a | ∀ᵐ ω ∂measIP, (1 + i) * (x + ∑ k, a k * R ω k) ∈ domU}

/-- `u(x,a) := 𝔼[U((1+i)(x + a·R))] ∈ [-∞, ∞)` (Bäuerle–Rieder, p. 77, PDF 91, unnumbered
display). -/
noncomputable def OnePeriodU (measIP : Measure Ω) (U : ℝ → ℝ) (i : ℝ) (R : Ω → Fin d → ℝ)
    (x : ℝ) (a : Fin d → ℝ) : EReal :=
  erealIntegral measIP (fun ω => (U ((1 + i) * (x + ∑ k, a k * R ω k)) : EReal))

/-- `v(x) := sup_{a ∈ D(x)} u(x,a)` (Bäuerle–Rieder, Eq. (4.2), p. 77, PDF 91). -/
noncomputable def OnePeriodV (measIP : Measure Ω) (domU : Set ℝ) (U : ℝ → ℝ) (i : ℝ)
    (R : Ω → Fin d → ℝ) (x : ℝ) : EReal :=
  ⨆ a ∈ OnePeriodD measIP domU i R x, OnePeriodU measIP U i R x a

/-- The one-period market has no arbitrage opportunities (Bäuerle–Rieder, Theorem 3.1.5(b),
p. 63, PDF 78, specialized to a single period): no `a ∈ ℝ^d` with `a·R ≥ 0` `ℙ`-a.s. and
`ℙ(a·R > 0) > 0`. -/
def NoArbitrageOnePeriod (measIP : Measure Ω) (R : Ω → Fin d → ℝ) : Prop :=
  ¬ ∃ a : Fin d → ℝ, (∀ᵐ ω ∂measIP, 0 ≤ ∑ k, a k * R ω k) ∧
    measIP {ω | 0 < ∑ k, a k * R ω k} > 0

end MDPFinance.TerminalWealth


