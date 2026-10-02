-- Prove2me | Definitions.Def_MDPFinance_BayesianModels_Orders
-- name    : MDPFinance_BayesianModels_Orders
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:18:32.557785+00:00
-- url     : https://prove2.me/theorems/2ca4a8f0-0655-49e4-a6aa-5d18d450cf39
-- title:
--   The likelihood ratio order and MTP2 functions
-- statement:
--   Two definitions from Appendix B.3/A.3, needed to state Lemma 5.4.9 and the goal Theorem
--   5.4.10.
--
--   **The likelihood ratio order** (Definition B.3.5) on two densities $f,g$ w.r.t. a common
--   dominating measure: $f \le_{lr} g$ iff $f(t)g(s) \le f(s)g(t)$ for all $s \le t$. The book
--   applies this directly to densities — e.g. $q_Z(\cdot\mid\theta,a) \le_{lr} q_Z(\cdot\mid\theta',a)$
--   — rather than to the underlying random variables, which is how it is formalized here.
--
--   **MTP2 (multivariate total positivity of order 2)** (Definition A.3.3): a function
--   $f : \mathbb R^d \to \mathbb R_{\ge 0}$ is MTP2 if $f(x)f(y) \le f(x\wedge y)f(x \vee y)$ for all
--   $x,y$ (componentwise meet/join). Specialized here to $d=2$, matching Lemma 5.4.9's use of
--   $q_Z(z\mid\theta,a)$ as a function of the pair $(z,\theta)$.
--
--   **Formalization Note.** Distinct from `MDPFinance.StructuredModels.LEStochasticOrder`/
--   `LEConcaveOrder` (chunk `02c`), which compare *measures* via test-function expectations rather
--   than *densities* via a ratio-monotonicity condition.
--
--   **Moderation note.** `LRMeasure` states Definition B.3.5 on measures: $\mu\le_{lr}\mu'$ iff *some* versions of their densities satisfy the ratio condition pointwise. The order on $I$ in the monotonicity results is defined through it, so that it does not depend on which versions $\hat p(\cdot\mid i)$ are chosen (a pointwise condition on fixed versions could be broken by changing a density on a null set).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 353, 360, Definitions A.3.3, B.3.5

import Mathlib

open MeasureTheory

namespace MDPFinance.BayesianModels

/-- The **likelihood ratio order** on real densities (Bäuerle–Rieder, Definition B.3.5, p. 360,
PDF 366, applied directly to two densities `f`, `g` w.r.t. a common dominating measure, as the
book itself writes `q_Z(\cdot|θ,a) ≤_{lr} q_Z(\cdot|θ',a)` and `\hat μ(\cdot|i) ≤_{lr}
\hat μ(\cdot|i')` for densities rather than for the underlying random variables): `f ≤_{lr} g` iff
`f(t) g(s) ≤ f(s) g(t)` for all `s ≤ t`. Distinct from `MDPFinance.StructuredModels.
LEStochasticOrder`/`LEConcaveOrder` (chunk `02c`), which compare measures via test-function
expectations, not densities via a ratio-monotonicity condition. -/
def LikelihoodRatioOrder (f g : ℝ → ℝ) : Prop :=
  ∀ s t : ℝ, s ≤ t → f t * g s ≤ f s * g t

/-- `μ ≤_{lr} μ'` for two measures on `ℝ` with densities w.r.t. a common dominating measure `ρ`
(Bäuerle–Rieder, Definition B.3.5, p. 360, PDF 366): *some* versions `f`, `g` of the densities
satisfy `f(t) g(s) ≤ f(s) g(t)` for all `s ≤ t`. Stated on the measures, so that it does not
depend on the versions chosen (the book's `\hat μ(\cdot|i) ≤_{lr} \hat μ(\cdot|i')`, p. 164). -/
def LRMeasure (ρ μ μ' : Measure ℝ) : Prop :=
  ∃ f g : ℝ → ℝ, Measurable f ∧ Measurable g ∧ (∀ θ, 0 ≤ f θ) ∧ (∀ θ, 0 ≤ g θ) ∧
    μ = ρ.withDensity (fun θ => ENNReal.ofReal (f θ)) ∧
    μ' = ρ.withDensity (fun θ => ENNReal.ofReal (g θ)) ∧ LikelihoodRatioOrder f g

/-- **MTP2** (multivariate total positivity of order 2) (Bäuerle–Rieder, Definition A.3.3, p. 353,
PDF 359): a function `f : ℝ^d → ℝ_{≥0}` is MTP2 if `f(x) f(y) ≤ f(x ∧ y) f(x ∨ y)` for all
`x, y`, where `∧`, `∨` are the componentwise min/max. Specialized here to `d = 2` (`ℝ × ℝ`,
matching Lemma 5.4.9's `q_Z(z|θ,a)` as a function of the pair `(z,θ)`), using `Prod`'s pointwise
lattice structure for `⊓`/`⊔`. -/
def IsMTP2 (f : ℝ × ℝ → ℝ) : Prop :=
  ∀ x y : ℝ × ℝ, f x * f y ≤ f (x ⊓ y) * f (x ⊔ y)

end MDPFinance.BayesianModels


