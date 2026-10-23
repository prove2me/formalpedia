-- Prove2me | Definitions.Def_CoVaRMC_Batching_Setting
-- name    : CoVaRMC_Batching_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:06.625899+00:00
-- url     : https://prove2.me/theorems/168cabbe-1d29-478a-bbd0-dcac7130ab2a
-- title:
--   §2–§3, pp. 4–11, Appendix A p. 31 — joint density model, conditional cdf (3), Assumption 1, the batching estimator Ŷ^BE, F̂_k, σ̂, A, y_k, c_{m,k}(t) and O_Pr
-- statement:
--   This file fixes the model and the estimator of Huang, Lin and Hong's batching estimator of CoVaR.
--
--   **Model (§2, pp. 4–5).** The pair of losses $(X, Y)$ has a joint density $f(x,y) \ge 0$ on $\mathbb R^2$ with $\int f = 1$; its law is Lebesgue measure with density $f$. The marginal density and distribution function of $X$ are
--   $$f_X(x) = \int_{\mathbb R} f(x,y)\,dy, \qquad F_X(x) = \int_{-\infty}^x f_X(u)\,du,$$
--   and the conditional distribution function and conditional density are, by Equation (3),
--   $$F_{Y|X}(y\mid x) = \int_{-\infty}^y \frac{f(x,v)}{f_X(x)}\,dv, \qquad f_{Y|X}(y\mid x) = \frac{f(x,y)}{f_X(x)}.$$
--   Since (3) is only meaningful where $f_X(x) > 0$, statements are made about a **version** $F_c(y, x)$ of $F_{Y|X}(y\mid x)$: any function of $(y, x)$ that agrees with (3) at every $x$ with $f_X(x) > 0$.
--
--   **Assumption 1 (p. 5).** For reals $v$ (playing $\mathrm{VaR}_\alpha(X)$) and $c$ (playing $\mathrm{CoVaR}_{\alpha,\beta}$), there are open sets $\mathcal X \ni v$ and $\mathcal Y \ni c$ such that
--
--   1. $f_X$ is continuously differentiable and positive on $\mathcal X$;
--   2. $f$ is continuously differentiable and positive on $\mathcal X \times \mathcal Y$;
--   3. for every $y \in \mathcal Y$, $x \mapsto F_{Y|X}(y\mid x)$ is twice differentiable on all of $\mathbb R$.
--
--   **Sample and estimator (§3.1, p. 6).** An i.i.d. array $(X_{i,j}, Y_{i,j})$ is split into $k$ batches of $m$ observations. In batch $i$, $X_{i,(\lceil \alpha m\rceil)}$ is the $\lceil \alpha m\rceil$-th smallest of $X_{i,1},\dots,X_{i,m}$ and $\hat Y_i = Y_{i,(\lceil \alpha m\rceil)}$ is the $Y$ **paired with** it (the concomitant, not an order statistic of the $Y$'s). The batching estimator is the $\lceil \beta k\rceil$-th smallest of $\hat Y_1, \dots, \hat Y_k$:
--   $$\hat Y^{\mathrm{BE}} = \hat Y_{(\lceil \beta k\rceil)}.$$
--   The empirical distribution function (p. 7), the batch probability and its standard deviation (Lemma 4, p. 10) are
--   $$\hat F_k(y) = \frac1k \sum_{i=1}^k I\{\hat Y_i \le y\}, \qquad p_m(y) = \mathrm E[I\{\hat Y \le y\}], \qquad \hat\sigma(y) = \sqrt{p_m(y)\,(1 - p_m(y))} = \sqrt{\mathrm{Var}(I\{\hat Y \le y\})}.$$
--
--   **Quantities of Appendix A (p. 31).** $A = \sqrt{\beta(1-\beta)}/f_{Y|X}(c\mid v)$, $y_k = c + tAk^{-1/2}$ and
--   $$c_{m,k}(t) = \frac{\sqrt k}{\hat\sigma(y_k)}\big(\beta - \mathrm E[I\{\hat Y \le y_k\}]\big).$$
--
--   **Boundedness in probability (p. 5).** $Z_\nu = O_{\Pr}(r_\nu)$ means: for every $\varepsilon > 0$ there is $C > 0$ such that $\Pr\{|Z_\nu / r_\nu| > C\} \le \varepsilon$ for **all** $\nu$.
--
--   These objects are the vocabulary of every statement of the mission, from the conditional density identity to Theorem 3.
--
--   **Formalization Note.** Order statistics and concomitants are the published `ImpactInvesting.Portfolio.orderStat` / `inducedOrderStat`, built on Mathlib's `Tuple.sort`, which breaks ties by index; ties among the $X$'s (and among the $\hat Y_i$) have probability zero because $(X, Y)$ has a density. Ranks are 0-based: the $\lceil qN\rceil$-th smallest of $N$ values has index $\min(\lceil qN\rceil - 1, N-1)$, and the clamp is inactive for $q \in (0,1)$, $N \ge 1$; an empty batch ($m = 0$) or $k = 0$ gives the value $0$, and every theorem assumes $k, m \ge 1$. Batch $i$ (0-based) uses the sample points $S(i, j)$, $j < m$, of an array indexed by $\mathbb N \times \mathbb N$; $\mathrm E[I\{\hat Y \le y\}]$ is computed on batch $0$ (the paper's first batch), which has the same law as every batch. The version $F_c$ takes $y$ first, as in $F_{Y|X}(y\mid x)$. "Neighbourhood" in Assumption 1 is an open set containing the point, which loses nothing. In (3), Lean's $a/0 = 0$ gives $F_{Y|X}(y\mid x) = 0$ where $f_X(x) = 0$; the sample avoids that set almost surely.
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, pp. 4–5, Equations (1)–(3), Assumption 1, O_Pr; p. 6, §3.1 Steps 1–3; p. 7, F̂_k; p. 10, Lemma 4 (σ̂); p. 31, Appendix A (A, y_k, c_{m,k}(t))

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat

namespace CoVaRMC.Batching

open MeasureTheory ProbabilityTheory Filter Topology

/-- §2, p. 5: a joint density `f` of the pair of losses `(X, Y)` on `ℝ × ℝ`. -/
structure JointDensity where
  /-- the joint density `f(x, y)` -/
  f : ℝ × ℝ → ℝ
  nonneg : ∀ p, 0 ≤ f p
  measurable : Measurable f
  integrable : Integrable f
  integral_eq_one : ∫ p, f p = 1

/-- The law of `(X, Y)`: Lebesgue measure on `ℝ × ℝ` with density `f`. -/
noncomputable def JointDensity.law (D : JointDensity) : Measure (ℝ × ℝ) :=
  volume.withDensity (fun p => ENNReal.ofReal (D.f p))

/-- p. 5: the marginal density `f_X(x) = ∫_ℝ f(x, y) dy`. -/
noncomputable def JointDensity.fX (D : JointDensity) (x : ℝ) : ℝ :=
  ∫ y, D.f (x, y)

/-- p. 5: the marginal distribution function `F_X(x) = ∫_{-∞}^x f_X(u) du`. -/
noncomputable def JointDensity.FX (D : JointDensity) (x : ℝ) : ℝ :=
  ∫ u in Set.Iic x, D.fX u

/-- Equation (3), p. 5: `F_{Y|X}(y | x) = ∫_{-∞}^y f(x, v) / f_X(x) dv`
(Lean's convention `a / 0 = 0` applies where `f_X(x) = 0`). -/
noncomputable def JointDensity.condCDF (D : JointDensity) (y x : ℝ) : ℝ :=
  (∫ v in Set.Iic y, D.f (x, v)) / D.fX x

/-- p. 5: the conditional density `f_{Y|X}(y | x) = f(x, y) / f_X(x)`. -/
noncomputable def JointDensity.condDensity (D : JointDensity) (y x : ℝ) : ℝ :=
  D.f (x, y) / D.fX x

/-- A version `Fc` of the conditional distribution function, defined at every `x`
(argument order `Fc y x = F_{Y|X}(y | x)`): it agrees with (3) wherever `f_X(x) > 0`. -/
def IsCondCDFVersion (D : JointDensity) (Fc : ℝ → ℝ → ℝ) : Prop :=
  ∀ x, 0 < D.fX x → ∀ y, Fc y x = D.condCDF y x

/-- Assumption 1, p. 5, for `v = VaR_α(X)` and `c = CoVaR_{α,β}`: `𝒳 ∋ v` and `𝒴 ∋ c` are open
neighbourhoods; `f_X` is continuously differentiable and positive on `𝒳`; `f` is continuously
differentiable and positive on `𝒳 × 𝒴`; for every `y ∈ 𝒴`, `x ↦ F_{Y|X}(y | x)` is twice
differentiable on `ℝ`. -/
def Assumption1 (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (v c : ℝ) (𝒳 𝒴 : Set ℝ) : Prop :=
  IsOpen 𝒳 ∧ v ∈ 𝒳 ∧ IsOpen 𝒴 ∧ c ∈ 𝒴 ∧
  ContDiffOn ℝ 1 D.fX 𝒳 ∧ (∀ x ∈ 𝒳, 0 < D.fX x) ∧
  ContDiffOn ℝ 1 D.f (𝒳 ×ˢ 𝒴) ∧ (∀ p ∈ 𝒳 ×ˢ 𝒴, 0 < D.f p) ∧
  ∀ y ∈ 𝒴, Differentiable ℝ (fun x => Fc y x) ∧ Differentiable ℝ (deriv (fun x => Fc y x))

/-- The 0-based index of the `⌈q N⌉`-th smallest of `N ≥ 1` values. The clamp `min … (N - 1)` is
inactive for `q ∈ (0, 1)`, where `1 ≤ ⌈q N⌉ ≤ N`. -/
noncomputable def rankIdx (q : ℝ) (N : ℕ) (hN : 0 < N) : Fin N :=
  ⟨min (⌈q * N⌉₊ - 1) (N - 1), by omega⟩

/-- §3.1, Step 2: `X_{i,(⌈αm⌉)}`, the `⌈αm⌉`-th order statistic of the `X`'s of batch `i`
(`S (i, j)`, `j < m`); `0` for an empty batch. -/
noncomputable def Xorder {Ω : Type*} (S : ℕ × ℕ → Ω → ℝ × ℝ) (α : ℝ) (m i : ℕ) (ω : Ω) : ℝ :=
  if h : 0 < m then
    ImpactInvesting.Portfolio.orderStat (fun j : Fin m => (S (i, j) ω).1) (rankIdx α m h)
  else 0

/-- §3.1, Step 2: `Ŷ_i = Y_{i,(⌈αm⌉)}`, the `Y` paired with the `⌈αm⌉`-th smallest `X` of batch `i`
(the concomitant, not an order statistic of the `Y`'s); `0` for an empty batch. -/
noncomputable def Yhat {Ω : Type*} (S : ℕ × ℕ → Ω → ℝ × ℝ) (α : ℝ) (m i : ℕ) (ω : Ω) : ℝ :=
  if h : 0 < m then
    ImpactInvesting.Portfolio.inducedOrderStat (fun j : Fin m => (S (i, j) ω).1)
      (fun j : Fin m => (S (i, j) ω).2) (rankIdx α m h)
  else 0

/-- §3.1, Step 3: the batching estimator `Ŷ^BE = Ŷ_(⌈βk⌉)`, the `⌈βk⌉`-th order statistic of
`Ŷ_1, …, Ŷ_k` (batches `0, …, k - 1`); `0` when `k = 0`. -/
noncomputable def YBE {Ω : Type*} (S : ℕ × ℕ → Ω → ℝ × ℝ) (α β : ℝ) (k m : ℕ) (ω : Ω) : ℝ :=
  if h : 0 < k then
    ImpactInvesting.Portfolio.orderStat (fun i : Fin k => Yhat S α m i ω) (rankIdx β k h)
  else 0

/-- The empirical distribution function `(1/k) #{i : w_i ≤ y}` of `w : Fin k → ℝ`. -/
noncomputable def empCDF {k : ℕ} (w : Fin k → ℝ) (y : ℝ) : ℝ :=
  (k : ℝ)⁻¹ * ((Finset.univ.filter fun i => w i ≤ y).card : ℝ)

/-- p. 7: `F̂_k(y) = (1/k) ∑_{i=1}^k I{Ŷ_i ≤ y}`. -/
noncomputable def FkHat {Ω : Type*} (S : ℕ × ℕ → Ω → ℝ × ℝ) (α : ℝ) (k m : ℕ) (y : ℝ) (ω : Ω) : ℝ :=
  empCDF (fun i : Fin k => Yhat S α m i ω) y

/-- `E[I{Ŷ ≤ y}] = Pr{Ŷ_1 ≤ y}` for batches of size `m` (batch `0` is the paper's first batch). -/
noncomputable def pHat {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : ℕ × ℕ → Ω → ℝ × ℝ)
    (α : ℝ) (m : ℕ) (y : ℝ) : ℝ :=
  (P {ω | Yhat S α m 0 ω ≤ y}).toReal

/-- Lemma 4, p. 10: `σ̂(y) = √Var(I{Ŷ ≤ y}) = √(p(1 - p))` with `p = E[I{Ŷ ≤ y}]`. -/
noncomputable def sigmaHat {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : ℕ × ℕ → Ω → ℝ × ℝ)
    (α : ℝ) (m : ℕ) (y : ℝ) : ℝ :=
  √(pHat P S α m y * (1 - pHat P S α m y))

/-- Appendix A, p. 31: `A = √(β(1 - β)) / f_{Y|X}(c | v)`, with `v = VaR_α(X)`, `c = CoVaR_{α,β}`. -/
noncomputable def Aconst (D : JointDensity) (β v c : ℝ) : ℝ :=
  √(β * (1 - β)) / D.condDensity c v

/-- Appendix A, p. 31: `y_k = c + t A k^{-1/2}`. -/
noncomputable def yk (c A t : ℝ) (k : ℕ) : ℝ :=
  c + t * A / √(k : ℝ)

/-- Appendix A, p. 31: `c_{m,k}(t) = (√k / σ̂(y_k)) (β - E[I{Ŷ ≤ y_k}])`. -/
noncomputable def cmk {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : ℕ × ℕ → Ω → ℝ × ℝ)
    (α β c A t : ℝ) (k m : ℕ) : ℝ :=
  √(k : ℝ) / sigmaHat P S α m (yk c A t k) * (β - pHat P S α m (yk c A t k))

/-- p. 5: `Z_ν = O_Pr(r_ν)`: for every `ε > 0` there is `C > 0` with `Pr{|Z_ν / r_ν| > C} ≤ ε`
for all `ν`. -/
def OPr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : ℕ → Ω → ℝ) (r : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ ν, P {ω | C < |Z ν ω / r ν|} ≤ ENNReal.ofReal ε

end CoVaRMC.Batching


