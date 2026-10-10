-- Prove2me | Definitions.Def_TailRiskSharing_TailConv_Setting
-- name    : TailRiskSharing_TailConv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:50.687834+00:00
-- url     : https://prove2.me/theorems/6c6eafd7-ecd2-4a19-99e5-e1721554e7ff
-- title:
--   §2.1–2.2 and §5, pp. 5, 17 — L^∞, law invariance for [−∞, ∞)-valued functionals, sup-norm continuity from above
-- statement:
--   Three further objects of Liu, Mao, Wang and Wei, built on the basic setting and the risk-measure vocabulary of the series.
--
--   1. **Bounded random variables.** $L^\infty$ is the set of essentially bounded random variables: measurable $X$ with $|X|\le C$ almost surely for some constant $C$ (§2.1).
--   2. **Law invariance for extended-real functionals.** A functional $F$ on a domain $\mathcal X$ with values in $[-\infty,\infty)$ (footnote 2) is *law-invariant* if $F(X)=F(Y)$ for all $X,Y\in\mathcal X$ with $F_X=F_Y$.
--   3. **Sup-norm continuity from above** (§5, p. 17). A real-valued risk measure $\rho$ on $\mathcal X$ is *continuous from above* (with respect to the sup-norm) if, for every sequence $(X_k)_{k\in\mathbb N}$ and every $X$ in $\mathcal X$ with $X_k\ge X$ a.s. for every $k$,
--   $$\operatorname*{ess\,sup}|X_k-X|\to 0\quad\Longrightarrow\quad \rho(X_k)\to\rho(X).$$
--
--   The continuity condition is the weak regularity assumption of Theorem 3; the paper notes that every monetary risk measure satisfies it.
--
--   **Formalization Note** The convergence $\operatorname{ess\,sup}|X_k-X|\to0$ is written as "for every $\eta>0$, eventually $|X_k-X|\le\eta$ almost surely", which is the same condition and avoids Lean's real essential supremum, whose value on an essentially unbounded function is a junk $0$. The paper defines sup-norm continuity and does not spell out "from above"; it is read as continuity along sequences that approach $X$ from above.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 5, §2.1 (L^∞), §2.2 (law invariance), footnote 2; p. 17, §5 (continuity with respect to the sup-norm)

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting
import Definitions.Def_TailRiskSharing_VaRTail_Setting

namespace TailRiskSharing.TailConv

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §2.1 p. 5: the domain `L^∞` of essentially bounded random variables. -/
def Linf (P : Measure Ω) : Set (Ω → ℝ) :=
  {X | Measurable X ∧ ∃ C : ℝ, ∀ᵐ ω ∂P, |X ω| ≤ C}

/-- §2.2 p. 5, for `[-∞, ∞)`-valued risk measures: law-invariant. -/
def IsLawInvariantE (P : Measure Ω) (dom : Set (Ω → ℝ)) (F : (Ω → ℝ) → EReal) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, (∀ x, TailRiskSharing.VaRConv.distFn P X x = TailRiskSharing.VaRConv.distFn P Y x) → F X = F Y

/-- §5 p. 17: (sup-norm) continuity from above: `ρ(X_k) → ρ(X)` whenever `X_k ≥ X` a.s. and
`ess-sup |X_k - X| → 0`. The convergence `ess-sup |X_k - X| → 0` is written as "for every `η > 0`,
eventually `|X_k - X| ≤ η` a.s.", which is the same condition and does not go through the real
`essSup`, whose value on an essentially unbounded function is a junk `0`. -/
def IsSupNormContinuousFromAbove (P : Measure Ω) (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ (Xs : ℕ → Ω → ℝ) (X : Ω → ℝ), (∀ k, Xs k ∈ dom) → X ∈ dom →
    (∀ k, ∀ᵐ ω ∂P, X ω ≤ Xs k ω) →
    (∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ᵐ ω ∂P, |Xs k ω - X ω| ≤ η) →
    Tendsto (fun k => ρ (Xs k)) atTop (𝓝 (ρ X))

end TailRiskSharing.TailConv


