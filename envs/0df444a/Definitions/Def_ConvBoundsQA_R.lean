-- Prove2me | Definitions.Def_ConvBoundsQA_R
-- name    : ConvBoundsQA_R
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:53.946202+00:00
-- url     : https://prove2.me/theorems/a155f359-f537-49bc-9c48-f34e28ab90a7
-- title:
--   RVaR $R_{\beta,\alpha}(\mu)$, ES and LES
-- statement:
--   For $\mu\in\mathcal M$ and $0\le\beta<\beta+\alpha\le 1$ the **range value-at-risk** (RVaR) is the average of the quantile of $\mu$ over $[1-\beta-\alpha,\,1-\beta]$:
--   $$
--   R_{\beta,\alpha}(\mu)=\frac1\alpha\int_\beta^{\beta+\alpha}q^+_{1-t}(\mu)\,\mathrm dt .
--   $$
--   It is finite when $\beta>0$ and $\alpha+\beta<1$, may be $+\infty$ or $-\infty$ when $\beta=0$ or $\alpha+\beta=1$, and for $(\beta,\alpha)=(0,1)$ it is the mean, defined only for distributions with a finite (or one-sided infinite) mean. The **expected shortfall** and the **left-tail expected shortfall** at level $\alpha$ are
--   $$
--   \mathrm{ES}_\alpha(\mu)=R_{0,\alpha}(\mu),\qquad \mathrm{LES}_\alpha(\mu)=R_{1-\alpha,\alpha}(\mu).
--   $$
--   The module also defines when the integral is well defined (its positive and negative parts are not both infinite) and when a finite family of extended reals contains no "$\infty-\infty$" (not both $+\infty$ and $-\infty$).
--
--   RVaR interpolates between quantiles ($\alpha\downarrow0$) and expected shortfall, and is the functional the convolution bounds are built from.
--
--   **Formalization Note** $R_{\beta,\alpha}(\mu)$ is $\alpha^{-1}$ times the difference, in `EReal`, of the lower integrals of the positive and negative parts of $t\mapsto q^+_{1-t}(\mu)$ over $[\beta,\beta+\alpha]$. When both parts are infinite (only possible for $(\beta,\alpha)=(0,1)$) the value is $-\infty$; the predicate `RDefined` excludes this case wherever it matters. Footnote 4 of the paper allows either $q^+$ or $q^-$ in the integrand.
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, §3, (6), p.7

import Mathlib
import Definitions.Def_ConvBoundsQA_qPlus

open MeasureTheory

namespace ConvBoundsQA

/-- The integral of the positive part of the quantile in (6):
`∫_β^{β+α} (q⁺_{1−t}(μ))⁺ dt ∈ [0, ∞]`
(Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, (6), p.7). -/
noncomputable def RPos (β α : ℝ) (μ : Measure ℝ) : ENNReal :=
  ∫⁻ t in Set.Icc β (β + α), (qPlus (1 - t) μ).toENNReal

/-- The integral of the negative part of the quantile in (6):
`∫_β^{β+α} (q⁺_{1−t}(μ))⁻ dt ∈ [0, ∞]`
(Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, (6), p.7). -/
noncomputable def RNeg (β α : ℝ) (μ : Measure ℝ) : ENNReal :=
  ∫⁻ t in Set.Icc β (β + α), (-qPlus (1 - t) μ).toENNReal

/-- The integral in (6) is well defined: the positive and the negative part are not both infinite.
By p.7 this can fail only for `(β, α) = (0, 1)` (the mean, "only well defined on the set `M₁`")
(Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, p.7). -/
def RDefined (β α : ℝ) (μ : Measure ℝ) : Prop :=
  RPos β α μ ≠ ⊤ ∨ RNeg β α μ ≠ ⊤

/-- The RVaR functional (6): for `0 ⩽ β < β + α ⩽ 1`,
`R_{β,α}(μ) = (1/α) ∫_β^{β+α} q⁺_{1−t}(μ) dt`, the average of the quantile of `μ` over
`[1 − β − α, 1 − β]` (Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, §3, (6), p.7).

**Formalization Note** The value lies in `EReal` (it may be `±∞` when `β = 0` or `α + β = 1`, p.7).
The integral is the difference of the integrals of the positive and negative parts of the quantile
over `t ∈ [β, β + α]`; footnote 4 (p.7) allows `q⁺` in the integrand. When both parts are infinite
(only possible for `(β, α) = (0, 1)`, where the page leaves `R_{0,1}` undefined outside `M₁`) the
`EReal` difference `⊤ − ⊤` is `⊥`; `RDefined` excludes that case wherever it matters. The value is
used only for `α > 0`. -/
noncomputable def R (β α : ℝ) (μ : Measure ℝ) : EReal :=
  ((α⁻¹ : ℝ) : EReal) * ((RPos β α μ : EReal) - (RNeg β α μ : EReal))

/-- Expected shortfall `ES_α(μ) = R_{0,α}(μ)` (Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, p.7). -/
noncomputable def ES (α : ℝ) (μ : Measure ℝ) : EReal := R 0 α μ

/-- Left-tail expected shortfall `LES_α(μ) = R_{1−α,α}(μ)`
(Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, p.7). -/
noncomputable def LES (α : ℝ) (μ : Measure ℝ) : EReal := R (1 - α) α μ

/-- A finite family of extended reals contains no `∞ − ∞`: it does not contain both `+∞` and `−∞`,
so its sum is the unambiguous one (Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, (9), p.8 and
Lemma EC.1, p.38: "provided the right-hand side … is well defined (not `∞ − ∞`)"). -/
def NoInfMinusInf {n : ℕ} (r : Fin n → EReal) : Prop :=
  ¬ ((∃ i, r i = ⊤) ∧ (∃ j, r j = ⊥))

end ConvBoundsQA


