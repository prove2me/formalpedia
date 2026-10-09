-- Prove2me | Definitions.Def_LimitedPriceChanges_AlgorithmI_Model
-- name    : LimitedPriceChanges_AlgorithmI_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:39.59703+00:00
-- url     : https://prove2.me/theorems/78b70e21-6557-439a-906a-df46077e00c3
-- title:
--   pp. 5–8 — the censored pricing-inventory model: demand pmf, profit G (4), G*, Assumption 1, Definition 1, §3 conditions
-- statement:
--   This file sets up the single-product pricing and inventory model of §2 with a scalar demand parameter (§3).
--
--   **Data.** Prices lie in $\mathcal P=[p^l,p^h]$ with $0\le p^l\le p^h$; order-up-to levels in $\mathcal Y=\{y^l,y^l+1,\dots,y^h\}$ with $y^l\le y^h$; the unknown parameter in $\mathcal Z=[z^l,z^h]$ with $0\le z^l\le z^h$. The holding cost is $h\ge0$ and the lost-sale cost $b\ge0$. Demand at price $p$ under parameter $z$ has probability mass function $f(\cdot;p,z)$ with support $\{d^l,d^l+1,\dots,d^h\}$, where $d^l$ is a nonnegative integer and $d^h\le+\infty$: for $p\in\mathcal P$ and $z\in\mathcal Z$, $f(d;p,z)>0$ exactly when $d^l\le d\le d^h$, the masses sum to $1$, and the mean $\mathbb E[D(p,z)]=\sum_d d\,f(d;p,z)$ is finite. Every order-up-to level is at least $d^l$ ($d^l\le y^l$).
--
--   **Profit.** With $\mathbb E[y-D]^+=\sum_{d<y}(y-d)f(d;p,z)$, $\mathbb E[D-y]^+=\sum_d\max(d-y,0)f(d;p,z)$, the single-period expected profit (4) is
--   $$
--   G(p,y,z)=p\,\mathbb E[D(p,z)]-h\,\mathbb E[y-D(p,z)]^+-(b+p)\,\mathbb E[D(p,z)-y]^+ .
--   $$
--   For a price selection $p^*_y(z)$ (an optimal solution of $\max_{p\in\mathcal P}G(p,y,z)$), the clairvoyant value is $G^*(z)=\max_{y\in\mathcal Y}G(p^*_y(z),y,z)$. The censored tail mass is $1-F(y-1;p,z)=\sum_{d\ge y}f(d;p,z)$.
--
--   **Conditions.**
--
--   1. $\mathbb E[D(p,z)]>0$ for every $p\in\mathcal P$ at the true $z$ (§2).
--   2. Every optimal order-up-to level exceeds $d^l$: if $G(p^*_y(z),y,z)=G^*(z)$ then $y>d^l$ (§3).
--   3. **Definition 1 (well-separated).** For every $p\in\mathcal P$, $f(\cdot;p,z_1)\ne f(\cdot;p,z_2)$ whenever $z_1\ne z_2\in\mathcal Z$.
--   4. **Assumption 1.** For every $d$ and $p\in\mathcal P$, $z\mapsto f(d;p,z)$ is differentiable on $\mathcal Z$, and with
--   $$
--   \underline I(p,z)=\frac{(\partial f(d^l;p,z)/\partial z)^2}{f(d^l;p,z)},\qquad I(p,z)=\sum_{d=d^l}^{d^h}\frac{(\partial f(d;p,z)/\partial z)^2}{f(d;p,z)},
--   $$
--   (i) $\underline I(p,z)\ge c_3>0$ and $I(p,z)<c_4<+\infty$ for all $p\in\mathcal P$, $z\in\mathcal Z$; (ii) $f(d;p,z)\ge c_5>0$ for all $p\in\mathcal P$, $z\in\mathcal Z$, $d\in\{d^l,\dots,y^h\}$; (iii) for every $p\in\mathcal P$, $f(d^l;p,z)$ is strictly monotone in $z\in\mathcal Z$.
--   5. Assumption A of the data-based optimization file, for this $G$ with $\|z'-z\|=|z'-z|$.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** Two hypotheses are added to the page and disclosed: differentiability of $z\mapsto f(d;p,z)$ on $\mathcal Z$, which the partial derivatives of Assumption 1 presuppose, and summability of $\sum_d d\,f(d;p,z)$, without which (4) is meaningless when $d^h=+\infty$. The condition $d^l\le y^l$ is the convention under which the two cases $\hat y>d^l$, $\hat y=d^l$ of Algorithm-I, Step 1 cover every $\hat y\in\mathcal Y$; the page never states the case $\hat y<d^l$. "The optimal order-up-to level is greater than $d^l$" is read for every optimal level. Derivatives in $z$ are taken within $\mathcal Z$. The Fisher information is an extended nonnegative real, so a divergent sum is $+\infty$ and cannot satisfy $I<c_4$; terms outside the support are $0$. Infinite sums are real `tsum`s, which are the true sums under the summability of the mean and of the pmf. Strictness $p^l<p^h$ and $z^l<z^h$ is not assumed; it follows from Assumption A(iii) (an interior point) and Assumption 1(i) ($\underline I>0$).
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), pp. 5–6 (§2, (1)–(4), G*, p*_y), p. 7 (Assumption A, §3 opening), p. 8 (Definition 1, Assumption 1)

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_DataBasedOptimization

namespace LimitedPriceChanges.AlgorithmI

/-! # The censored pricing-inventory system of §2 and §3

Chen, Chao and Wang, *Data-Based Dynamic Pricing and Inventory Control with Censored Demand and
Limited Price Changes*, SSRN 2700747 (revision of 2020-02-10), pp. 5–8: the model (1)–(4),
the single-period profit `G`, the benchmark `G*`, Assumption A, the §3 conditions,
Definition 1 and Assumption 1, for a scalar parameter `z ∈ 𝒵 = [zl, zh]`. -/

/-- The data of the §2 model with scalar parameter (§3, p. 7), and its standing conditions:
* prices `𝒫 = [pl, ph]` with `0 ≤ pl ≤ ph`; order-up-to levels `𝒴 = {yl, …, yh}` with
  `yl ≤ yh`; parameters `𝒵 = [zl, zh]` with `0 ≤ zl ≤ zh`;
* holding cost `h ≥ 0` and lost-sale cost `b ≥ 0`;
* the demand pmf `f d p z = f(d; p, z)` with support `{dl, dl + 1, …, dh}`, `dh ∈ ℕ ∪ {+∞}`:
  for every `p ∈ 𝒫` and `z ∈ 𝒵`, `f(d; p, z) > 0` exactly when `dl ≤ d ≤ dh`, and the masses
  sum to `1`; the mean `∑ d f(d; p, z)` is finite;
* `dl ≤ yl`: every order-up-to level is at least the known demand lower bound, so the two cases
  `ŷ > dl` and `ŷ = dl` of Algorithm-I, Step 1 (p. 9) cover every `ŷ ∈ 𝒴`. -/
structure Model where
  pl : ℝ
  ph : ℝ
  yl : ℕ
  yh : ℕ
  dl : ℕ
  dh : ℕ∞
  zl : ℝ
  zh : ℝ
  h : ℝ
  b : ℝ
  f : ℕ → ℝ → ℝ → ℝ
  pl_nonneg : 0 ≤ pl
  pl_le_ph : pl ≤ ph
  yl_le_yh : yl ≤ yh
  dl_le_yl : dl ≤ yl
  zl_nonneg : 0 ≤ zl
  zl_le_zh : zl ≤ zh
  h_nonneg : 0 ≤ h
  b_nonneg : 0 ≤ b
  f_pos_iff : ∀ p ∈ Set.Icc pl ph, ∀ z ∈ Set.Icc zl zh, ∀ d : ℕ,
    0 < f d p z ↔ (dl ≤ d ∧ (d : ℕ∞) ≤ dh)
  f_nonneg : ∀ p ∈ Set.Icc pl ph, ∀ z ∈ Set.Icc zl zh, ∀ d : ℕ, 0 ≤ f d p z
  f_hasSum : ∀ p ∈ Set.Icc pl ph, ∀ z ∈ Set.Icc zl zh, HasSum (fun d => f d p z) 1
  mean_summable : ∀ p ∈ Set.Icc pl ph, ∀ z ∈ Set.Icc zl zh,
    Summable (fun d : ℕ => (d : ℝ) * f d p z)

namespace Model

variable (S : Model)

/-- The price interval `𝒫 = [pl, ph]`. -/
def P : Set ℝ := Set.Icc S.pl S.ph

/-- The order-up-to levels `𝒴 = {yl, yl + 1, …, yh}`. -/
def Y : Finset ℕ := Finset.Icc S.yl S.yh

theorem Y_nonempty : S.Y.Nonempty := Finset.nonempty_Icc.mpr S.yl_le_yh

/-- The parameter interval `𝒵 = [zl, zh]`. -/
def Z : Set ℝ := Set.Icc S.zl S.zh

/-- `𝔼[D(p, z)] = ∑_d d f(d; p, z)`. -/
noncomputable def meanDemand (p z : ℝ) : ℝ := ∑' d : ℕ, (d : ℝ) * S.f d p z

/-- `𝔼[y − D(p, z)]⁺ = ∑_{d < y} (y − d) f(d; p, z)` (a finite sum). -/
noncomputable def expLeftover (p : ℝ) (y : ℕ) (z : ℝ) : ℝ :=
  ∑ d ∈ Finset.range y, ((y : ℝ) - d) * S.f d p z

/-- `𝔼[D(p, z) − y]⁺ = ∑_d max(d − y, 0) f(d; p, z)`. -/
noncomputable def expLostSales (p : ℝ) (y : ℕ) (z : ℝ) : ℝ :=
  ∑' d : ℕ, max ((d : ℝ) - y) 0 * S.f d p z

/-- The censored tail mass `1 − F(y − 1; p, z) = ℙ{D(p, z) ≥ y} = ∑_{d ≥ y} f(d; p, z)`. -/
noncomputable def tail (y : ℕ) (p z : ℝ) : ℝ :=
  ∑' d : ℕ, if y ≤ d then S.f d p z else 0

/-- The single-period expected profit (4), p. 6:
`G(p, y, z) = p 𝔼[D(p, z)] − h 𝔼[y − D(p, z)]⁺ − (b + p) 𝔼[D(p, z) − y]⁺`. -/
noncomputable def G (p : ℝ) (y : ℕ) (z : ℝ) : ℝ :=
  p * S.meanDemand p z - S.h * S.expLeftover p y z - (S.b + p) * S.expLostSales p y z

/-- The clairvoyant optimal value `G*(z) = max_{y ∈ 𝒴} G(p*_y(z), y, z)` (p. 6), for a price
selection `pstar` (`p*_y(z)`). When `pstar` is a price selection this is
`max_{(p, y) ∈ 𝒫 × 𝒴} G(p, y, z)`. -/
noncomputable def Gstar (pstar : ℕ → ℝ → ℝ) (z : ℝ) : ℝ :=
  optValue S.Y S.Y_nonempty S.G pstar z

/-- `I̲(p, z) = (∂f(dl; p, z)/∂z)² / f(dl; p, z)` (Assumption 1(i), p. 8); the derivative is
taken within `𝒵`. -/
noncomputable def fisherLow (p z : ℝ) : ℝ :=
  (derivWithin (fun z' => S.f S.dl p z') S.Z z) ^ 2 / S.f S.dl p z

/-- The Fisher information `I(p, z) = ∑_{d = dl}^{dh} (∂f(d; p, z)/∂z)² / f(d; p, z)`
(Assumption 1(i), p. 8), as an extended nonnegative real (a divergent sum is `+∞`, not `0`).
The terms with `d` outside the support `{dl, …, dh}` are `0` (there `f = 0`, and `x / 0 = 0`). -/
noncomputable def fisher (p z : ℝ) : ENNReal :=
  ∑' d : ℕ, ENNReal.ofReal ((derivWithin (fun z' => S.f d p z') S.Z z) ^ 2 / S.f d p z)

/-- §2, p. 5: `𝔼[D(p, z)] > 0` for every `p ∈ 𝒫`, at the true parameter `z`. -/
def MeanPos (z : ℝ) : Prop := ∀ p ∈ S.P, 0 < S.meanDemand p z

/-- §3, p. 7: "the optimal order-up-to level is greater than `dl`", read for every optimal
level: every `y ∈ 𝒴` with `G(p*_y(z), y, z) = G*(z)` satisfies `y > dl`. -/
def OptLevelAboveDl (pstar : ℕ → ℝ → ℝ) (z : ℝ) : Prop :=
  ∀ y ∈ S.Y, S.G (pstar y z) y z = S.Gstar pstar z → S.dl < y

/-- **Definition 1** (p. 8): the family is well-separated: for every `p ∈ 𝒫`, the pmfs
`{f(·; p, z) : z ∈ 𝒵}` are identifiable, i.e. `f(·; p, z₁) ≠ f(·; p, z₂)` for `z₁ ≠ z₂ ∈ 𝒵`. -/
def WellSeparated : Prop :=
  ∀ p ∈ S.P, ∀ z₁ ∈ S.Z, ∀ z₂ ∈ S.Z, z₁ ≠ z₂ → (fun d => S.f d p z₁) ≠ (fun d => S.f d p z₂)

/-- **Assumption 1** (p. 8), with the differentiability of `z ↦ f(d; p, z)` on `𝒵` that the
partial derivatives presuppose:
* (i) `I̲(p, z) ≥ c₃ > 0` and `I(p, z) < c₄ < +∞` for all `p ∈ 𝒫`, `z ∈ 𝒵`;
* (ii) `f(d; p, z) ≥ c₅ > 0` for all `p ∈ 𝒫`, `z ∈ 𝒵`, `d ∈ {dl, …, yh}`;
* (iii) for every `p ∈ 𝒫`, `z ↦ f(dl; p, z)` is strictly monotone on `𝒵`. -/
structure Assumption1 : Prop where
  differentiable : ∀ d : ℕ, ∀ p ∈ S.P, DifferentiableOn ℝ (fun z' => S.f d p z') S.Z
  fisherLow_ge : ∃ c₃ : ℝ, 0 < c₃ ∧ ∀ p ∈ S.P, ∀ z ∈ S.Z, c₃ ≤ S.fisherLow p z
  fisher_lt : ∃ c₄ : ℝ, ∀ p ∈ S.P, ∀ z ∈ S.Z, S.fisher p z < ENNReal.ofReal c₄
  f_ge : ∃ c₅ : ℝ, 0 < c₅ ∧ ∀ p ∈ S.P, ∀ z ∈ S.Z, ∀ d : ℕ, S.dl ≤ d → d ≤ S.yh →
    c₅ ≤ S.f d p z
  strictMono : ∀ p ∈ S.P,
    StrictMonoOn (fun z' => S.f S.dl p z') S.Z ∨ StrictAntiOn (fun z' => S.f S.dl p z') S.Z

/-- Assumption A (p. 7) for this model, at the true `z`, with `‖·‖ = |·|` on `𝒵 ⊂ ℝ`. -/
def AssumptionA (pstar : ℕ → ℝ → ℝ) (z : ℝ) : Prop :=
  LimitedPriceChanges.AlgorithmI.AssumptionA S.pl S.ph S.Y S.Y_nonempty S.Z S.G pstar z

/-- `pstar` is the price selection `p*_y(z')` on `𝒵` (p. 6 and Assumption A(iii)). -/
def IsPriceSelection (pstar : ℕ → ℝ → ℝ) : Prop :=
  LimitedPriceChanges.AlgorithmI.IsPriceSelection S.pl S.ph S.Y S.Z S.G pstar

end Model

end LimitedPriceChanges.AlgorithmI


