-- Prove2me | Definitions.Def_ConvBoundsQA_convBound
-- name    : ConvBoundsQA_convBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:53.655702+00:00
-- url     : https://prove2.me/theorems/d37a5c6a-50dd-4e5a-a10a-214681d5f756
-- title:
--   The convolution bound $\inf_{\beta}\sum_i R_{\beta_i,\beta_0}(\mu_i)$
-- statement:
--   For $\mu\in\mathcal M^n$ and a set $S$ of parameters $\beta=(\beta_0,\beta_1,\dots,\beta_n)$, the **convolution bound** over $S$ is
--   $$
--   \inf_{\beta\in S}\ \sum_{i=1}^n R_{\beta_i,\beta_0}(\mu_i),
--   $$
--   the infimum being taken over the $\beta$ for which the sum is well defined, i.e. every term is defined and the terms do not contain both $+\infty$ and $-\infty$. For $S=(1-t)\Delta_n$ this is the right-hand side of (14); for $S=\{\beta\in(t+s)\Delta_n':\beta_0\ge s\}$ it is the right-hand side of (11)/(12).
--
--   **Formalization Note** The infimum is in `EReal`; excluding a $\beta$ whose terms contain both $\pm\infty$ is the same as valuing that sum $+\infty$. Sums with only $+\infty$ (or only $-\infty$) terms are kept. The infimum over an empty family is $+\infty$.
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, (11), p.8; (12), p.9; (14), p.11

import Mathlib
import Definitions.Def_ConvBoundsQA_R

open MeasureTheory

namespace ConvBoundsQA

/-- The terms `R_{βᵢ,β₀}(μᵢ)`, `i = 1, …, n`, of the convolution bound for `β = (β₀, β₁, …, βₙ)`
(Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, (11), p.8; (12), p.9; (14), p.11). -/
noncomputable def convTerms {n : ℕ} (μ : Fin n → Measure ℝ) (β : ℝ × (Fin n → ℝ)) : Fin n → EReal :=
  fun i => R (β.2 i) β.1 (μ i)

/-- The sum `Σᵢ R_{βᵢ,β₀}(μᵢ)` is well defined: every term is defined and the terms do not contain
both `+∞` and `−∞` (Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, (9)–(10), p.8). -/
def SumDefined {n : ℕ} (μ : Fin n → Measure ℝ) (β : ℝ × (Fin n → ℝ)) : Prop :=
  (∀ i, RDefined (β.2 i) β.1 (μ i)) ∧ NoInfMinusInf (convTerms μ β)

/-- The convolution bound over a parameter set `S`:
`inf_{β ∈ S} Σ_{i=1}^n R_{βᵢ,β₀}(μᵢ)` (Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, (11), p.8;
(12), p.9; (14), p.11).

**Formalization Note** The infimum is taken in `EReal` over the `β ∈ S` whose sum is well defined
(`SumDefined`): a `β` whose terms contain both `+∞` and `−∞` is left out, which is the same as giving
that sum the value `+∞`. Only such mixed sums are left out; a `β` with only `+∞` (or only `−∞`)
terms stays. The infimum of the empty family is `+∞`. -/
noncomputable def convBound {n : ℕ} (μ : Fin n → Measure ℝ) (S : Set (ℝ × (Fin n → ℝ))) : EReal :=
  ⨅ β ∈ S, ⨅ (_ : SumDefined μ β), ∑ i, convTerms μ β i

end ConvBoundsQA


