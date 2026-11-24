-- Prove2me | Definitions.Def_ConformalizedQuantileRegression_Basic
-- name    : ConformalizedQuantileRegression_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T07:39:25.636392+00:00
-- url     : https://prove2.me/theorems/8f25dab9-4e0d-42bb-8174-9b825f072f3e
-- title:
--   Empirical quantiles, exchangeability and the split CQR interval
-- statement:
--   Objects of Sections 1 and 4 and Appendix A of Romano, Patterson and Candès (2019).
--
--   1. **Data.** A sample is a pair $(x,y)\in\mathbb{R}^p\times\mathbb{R}$. The training samples are $(X_1,Y_1),\dots,(X_n,Y_n)$ and the test sample is $(X_{n+1},Y_{n+1})$.
--   2. **Empirical CDF and quantile (Appendix A).** For real values $z_i$, $i\in s$, with $s$ a finite index set, $\hat F(y)=\frac{1}{|s|}\sum_{i\in s}1\{z_i\le y\}$ and $\hat Q(\beta)=\inf\{y\in\mathbb{R}:\beta\le\hat F(y)\}$, taken in the extended reals $[-\infty,+\infty]$. In particular $\hat Q(\beta)=+\infty$ when $\beta>1$. The order statistic $Z_{(k)}$ is the $k$-th smallest of the values, counted with multiplicity.
--   3. **Exchangeability.** Random variables $V_1,\dots,V_m$ on a probability space are exchangeable if they are measurable and $(V_{\sigma(1)},\dots,V_{\sigma(m)})$ has the same joint law as $(V_1,\dots,V_m)$ for every permutation $\sigma$.
--   4. **Algorithm 1.** The index set $\{1,\dots,n\}$ is split into a proper training set $\mathcal I_1$ and a calibration set $\mathcal I_2$. A quantile regression algorithm $\mathcal A$ maps the proper training data $\{(X_i,Y_i):i\in\mathcal I_1\}$ to two functions $\hat q_{\mathrm{lo}},\hat q_{\mathrm{hi}}:\mathbb{R}^p\to\mathbb{R}$. It is called measurable if $(\text{training data},x)\mapsto\hat q_{\mathrm{lo}}(x)$ and $(\text{training data},x)\mapsto\hat q_{\mathrm{hi}}(x)$ are jointly measurable.
--   5. **Conformity score (eq. 9).** $E=\max\{\hat q_{\mathrm{lo}}(X)-Y,\;Y-\hat q_{\mathrm{hi}}(X)\}$.
--   6. **CQR interval (eqs. 10-11).** $Q_{1-\alpha}(E,\mathcal I_2)$ is the $(1-\alpha)(1+1/|\mathcal I_2|)$-th empirical quantile of $\{E_i:i\in\mathcal I_2\}$, and $C(x)=[\hat q_{\mathrm{lo}}(x)-Q_{1-\alpha}(E,\mathcal I_2),\ \hat q_{\mathrm{hi}}(x)+Q_{1-\alpha}(E,\mathcal I_2)]$.
--   7. **Asymmetric interval (Theorem 2).** With the one-sided scores $E_{\mathrm{lo},i}=\hat q_{\mathrm{lo}}(X_i)-Y_i$ and $E_{\mathrm{hi},i}=Y_i-\hat q_{\mathrm{hi}}(X_i)$ and levels $\beta_{\mathrm{lo}},\beta_{\mathrm{hi}}$, $C(x)=[\hat q_{\mathrm{lo}}(x)-Q_{\beta_{\mathrm{lo}}}(E_{\mathrm{lo}},\mathcal I_2),\ \hat q_{\mathrm{hi}}(x)+Q_{\beta_{\mathrm{hi}}}(E_{\mathrm{hi}},\mathcal I_2)]$.
--
--   **Formalization Note** $\mathbb{R}^p$ is written as functions $\mathrm{Fin}\,p\to\mathbb{R}$ with the product σ-algebra (the Borel σ-algebra of $\mathbb{R}^p$). Empirical quantiles take values in the extended reals so that a level above $1$ gives $+\infty$ and the interval is then all of $\mathbb{R}$; this is the convention under which the paper's formulas (10)-(11) and Lemma 2 make sense when the inflated level exceeds $1$. The fitted functions are a function of the proper training data only, which is how Algorithm 1 uses $\mathcal A$. The levels of the asymmetric interval are arguments, so the paper's printed choice and the inflated choice used by its proof are both expressible.
-- source:
--   Romano, Patterson and Candès, Conformalized Quantile Regression, arXiv:1905.03222v1 (2019), Section 1 (exchangeability), Section 4 (Algorithm 1, eqs. (9)-(11), Theorem 2), Appendix A (empirical CDF, empirical quantile, order statistics), pp. 2, 4-7, 18

import Mathlib

/-!
Romano, Patterson and Candès, *Conformalized Quantile Regression*, arXiv:1905.03222v1 (2019):
empirical distribution functions, empirical quantiles and order statistics (Appendix A),
exchangeability (Section 1), the split of the data and the quantile regression algorithm
(Section 4, Algorithm 1), the conformity scores (eq. (9)), the conformalized prediction
interval (eqs. (10)-(11)), and the one-sided scores and asymmetric interval of Theorem 2.
-/

open MeasureTheory

noncomputable section

namespace ConformalizedQuantileRegression

/-- Section 1, p. 2: a feature vector `x ∈ ℝ^p`. -/
abbrev Feat (p : ℕ) : Type := Fin p → ℝ

/-- Section 1, p. 2 and Algorithm 1: a sample `(x, y) ∈ ℝ^p × ℝ`. -/
abbrev Sample (p : ℕ) : Type := Feat p × ℝ

/-- Appendix A, p. 18: the empirical CDF `F̂(y) = (1/|s|) ∑_{i ∈ s} 1{z_i ≤ y}` of the values
`z_i`, `i ∈ s` (for `s = {1, …, n}` this is `F̂_n`). -/
def empCDF {ι : Type*} (s : Finset ι) (z : ι → ℝ) (y : ℝ) : ℝ :=
  ((s.filter fun i => z i ≤ y).card : ℝ) / (s.card : ℝ)

/-- Appendix A, p. 18: the empirical quantile `Q̂(β) = inf {y ∈ ℝ : β ≤ F̂(y)}` of the values
`z_i`, `i ∈ s`, taken in the extended reals; it is `+∞` when the set is empty (level `β > 1`),
the convention needed by eqs. (10)-(11) and Lemma 2 when the inflated level exceeds `1`. -/
def empQuantile {ι : Type*} (s : Finset ι) (z : ι → ℝ) (β : ℝ) : EReal :=
  ⨅ (y : ℝ) (_ : β ≤ empCDF s z y), (y : EReal)

/-- Appendix A, p. 18: the order statistic `Z_(k)`, the `k`-th smallest of the values `z_i`,
`i ∈ s`, counted with multiplicity (used only for `1 ≤ k ≤ |s|`). -/
def orderStat {ι : Type*} (s : Finset ι) (z : ι → ℝ) (k : ℕ) : ℝ :=
  ((s.val.map z).sort (· ≤ ·)).getD (k - 1) 0

/-- Section 1, p. 2 and Appendix A: the random variables `V_1, …, V_m` (measurable maps on a
probability space) are exchangeable: `(V_{σ(1)}, …, V_{σ(m)})` and `(V_1, …, V_m)` have the
same joint law for every permutation `σ`. -/
def IsExchangeable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {m : ℕ}
    (P : Measure Ω) (V : Fin m → Ω → E) : Prop :=
  (∀ i, Measurable (V i)) ∧
    ∀ σ : Equiv.Perm (Fin m),
      Measure.map (fun ω i => V (σ i) ω) P = Measure.map (fun ω i => V i ω) P

/-- Section 4, p. 4 and Algorithm 1: a quantile regression algorithm `A` maps the proper
training set `{(X_i, Y_i) : i ∈ I₁}` to the pair `(q̂_lo, q̂_hi)` of fitted lower and upper
conditional quantile functions. -/
abbrev QRAlgorithm (p : ℕ) {n : ℕ} (I₁ : Finset (Fin n)) : Type :=
  (↥I₁ → Sample p) → (Feat p → ℝ) × (Feat p → ℝ)

/-- Standing measurability convention for Algorithm 1: the maps
`(training set, x) ↦ q̂_lo(x)` and `(training set, x) ↦ q̂_hi(x)` are measurable. -/
def IsMeasurableAlgorithm {p n : ℕ} {I₁ : Finset (Fin n)} (A : QRAlgorithm p I₁) : Prop :=
  Measurable (fun q : (↥I₁ → Sample p) × Feat p => (A q.1).1 q.2) ∧
    Measurable (fun q : (↥I₁ → Sample p) × Feat p => (A q.1).2 q.2)

/-- Algorithm 1, p. 5: `{q̂_lo, q̂_hi} ← A({(X_i, Y_i) : i ∈ I₁})`, the quantile functions fitted
on the proper training set of the data `d = ((X_1, Y_1), …, (X_n, Y_n))`. -/
def fitQR {p n : ℕ} {I₁ : Finset (Fin n)} (A : QRAlgorithm p I₁) (d : Fin n → Sample p) :
    (Feat p → ℝ) × (Feat p → ℝ) :=
  A (fun i => d i.1)

/-- Eq. (9), p. 4: the conformity score `E = max {q̂_lo(X) - Y, Y - q̂_hi(X)}` of a sample
`(X, Y)`. -/
def conformityScore {p : ℕ} (qlo qhi : Feat p → ℝ) (z : Sample p) : ℝ :=
  max (qlo z.1 - z.2) (z.2 - qhi z.1)

/-- Eq. (11), p. 5: `Q_{1-α}(E, I₂)`, the `(1 - α)(1 + 1/|I₂|)`-th empirical quantile of the
conformity scores `{E_i : i ∈ I₂}` of the calibration set. -/
def cqrCorrection {p n : ℕ} {I₁ : Finset (Fin n)} (A : QRAlgorithm p I₁) (I₂ : Finset (Fin n))
    (α : ℝ) (d : Fin n → Sample p) : EReal :=
  empQuantile I₂ (fun i => conformityScore (fitQR A d).1 (fitQR A d).2 (d i))
    ((1 - α) * (1 + 1 / (I₂.card : ℝ)))

/-- Eq. (10), p. 5 and Algorithm 1: the CQR prediction interval
`C(x) = [q̂_lo(x) - Q_{1-α}(E, I₂), q̂_hi(x) + Q_{1-α}(E, I₂)]`, as a set of reals (all of `ℝ`
when `Q_{1-α}(E, I₂) = +∞`). -/
def cqrInterval {p n : ℕ} {I₁ : Finset (Fin n)} (A : QRAlgorithm p I₁) (I₂ : Finset (Fin n))
    (α : ℝ) (d : Fin n → Sample p) (x : Feat p) : Set ℝ :=
  {y | ((fitQR A d).1 x : EReal) - cqrCorrection A I₂ α d ≤ (y : EReal) ∧
    (y : EReal) ≤ ((fitQR A d).2 x : EReal) + cqrCorrection A I₂ α d}

/-- Theorem 2, p. 7: the lower one-sided score `q̂_lo(X) - Y` of a sample `(X, Y)`. -/
def loScore {p : ℕ} (qlo : Feat p → ℝ) (z : Sample p) : ℝ := qlo z.1 - z.2

/-- Theorem 2, p. 7: the upper one-sided score `Y - q̂_hi(X)` of a sample `(X, Y)`. -/
def hiScore {p : ℕ} (qhi : Feat p → ℝ) (z : Sample p) : ℝ := z.2 - qhi z.1

/-- Theorem 2, p. 7: `Q_β(E_lo, I₂)`, the `β`-th empirical quantile of
`{q̂_lo(X_i) - Y_i : i ∈ I₂}` (the paper uses the level `β = 1 - α_lo`). -/
def loCorrection {p n : ℕ} {I₁ : Finset (Fin n)} (A : QRAlgorithm p I₁) (I₂ : Finset (Fin n))
    (β : ℝ) (d : Fin n → Sample p) : EReal :=
  empQuantile I₂ (fun i => loScore (fitQR A d).1 (d i)) β

/-- Theorem 2, p. 7: `Q_β(E_hi, I₂)`, the `β`-th empirical quantile of
`{Y_i - q̂_hi(X_i) : i ∈ I₂}` (the paper uses the level `β = 1 - α_hi`). -/
def hiCorrection {p n : ℕ} {I₁ : Finset (Fin n)} (A : QRAlgorithm p I₁) (I₂ : Finset (Fin n))
    (β : ℝ) (d : Fin n → Sample p) : EReal :=
  empQuantile I₂ (fun i => hiScore (fitQR A d).2 (d i)) β

/-- Theorem 2, p. 7: the asymmetric prediction interval
`C(x) = [q̂_lo(x) - Q_{βlo}(E_lo, I₂), q̂_hi(x) + Q_{βhi}(E_hi, I₂)]` with separate levels for the
two tails. -/
def asymInterval {p n : ℕ} {I₁ : Finset (Fin n)} (A : QRAlgorithm p I₁) (I₂ : Finset (Fin n))
    (βlo βhi : ℝ) (d : Fin n → Sample p) (x : Feat p) : Set ℝ :=
  {y | ((fitQR A d).1 x : EReal) - loCorrection A I₂ βlo d ≤ (y : EReal) ∧
    (y : EReal) ≤ ((fitQR A d).2 x : EReal) + hiCorrection A I₂ βhi d}

end ConformalizedQuantileRegression


