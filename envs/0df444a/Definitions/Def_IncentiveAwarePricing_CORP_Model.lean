-- Prove2me | Definitions.Def_IncentiveAwarePricing_CORP_Model
-- name    : IncentiveAwarePricing_CORP_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:49.65342+00:00
-- url     : https://prove2.me/theorems/0fa0b598-ff35-49f5-9531-494477c7ae46
-- title:
--   §3, pp. 11–16 — noise density and CDF, Assumption 1, feature law, valuations (1), lazy second-price auction with personalized reserves, the reserve problem (4)/(10), −log with −log 0 = +∞
-- statement:
--   This file fixes the one-period objects of the contextual auction model of Golrezaei, Javanmard and Mirrokni (§3, pp. 11–16).
--
--   1. **Features.** A feature (context) vector is a point $x\in\mathbb R^d$ with the Euclidean inner product $\langle\cdot,\cdot\rangle$. A **feature law** is a probability measure $\mathcal D$ on $\mathbb R^d$ with $\|x\|\le 1$ almost surely (p. 12). Its second-moment matrix $\Sigma=\mathbb E[xx^\top]$ satisfies, for every $u\neq 0$,
--   $$\frac{c_{\min}}{d}\|u\|^2<\mathbb E\big[\langle x,u\rangle^2\big]\le\frac{c_{\max}}{d}\|u\|^2 ,$$
--   the eigenvalue bounds used on p. 57 (footnote 16) and pp. 72–73.
--   2. **Noise.** For $B_n>0$, the noise density $f:\mathbb R\to\mathbb R$ is nonnegative, vanishes outside $[-B_n,B_n]$, is continuous on $[-B_n,B_n]$, has total mass $\int_{-B_n}^{B_n}f=1$ and mean zero $\int_{-B_n}^{B_n}zf(z)\,dz=0$ (p. 12). Its distribution function is $F(z)=\int_{(-\infty,z]}f$, so $F=0$ below $-B_n$ and $F=1$ above $B_n$ (footnote 12, p. 20); the law of one noise term is Lebesgue measure with density $f$.
--   3. **Assumption 1** (Log-concavity, p. 12): $F$ and $1-F$ are log-concave on $[-B_n,B_n]$.
--   4. **Valuations** (1): with preference vectors $\beta_i\in\mathbb R^d$ and noises $z_i$, buyer $i$'s valuation is $v_i=\langle x,\beta_i\rangle+z_i$.
--   5. **Lazy second-price auction with personalized reserves** (pp. 13–14): given bids $b\in\mathbb R^N$ and reserves $r\in\mathbb R^N$, let $i^\star$ be the highest bidder. If $b_{i^\star}\ge r_{i^\star}$ he gets the item ($q_{i^\star}=1$) and pays
--   $$p_{i^\star}=\max\Big\{r_{i^\star},\ \max_{j\neq i^\star}b_j\Big\};$$
--   every other buyer has $q_i=0$, $p_i=0$. The seller's revenue is $\sum_i p_iq_i$. When $N=1$ the inner maximum is over the empty set and the payment is $r_{i^\star}$.
--   6. **The reserve problem** (4), (10): for an index $\theta=\langle x,\beta\rangle$, the objective is $y\mapsto y\,(1-F(y-\theta))$. A **reserve rule** is a function $\mathrm{res}:\mathbb R\to\mathbb R$ such that $\mathrm{res}(\theta)$ maximizes this objective over all $y\in\mathbb R$, for every $\theta$.
--   7. **Negative logarithm**: $\mathrm{nll}(p)=-\log p$ for $p>0$ and $\mathrm{nll}(p)=+\infty$ for $p\le 0$, valued in $[0,+\infty]$; it is used in the likelihood (9).
--
--   These objects are shared by every statement of the mission: Proposition 3.1, Lemmas 1–3 and the definitions of the CORP policy and its regret.
--
--   **Formalization Note** Log-concavity is the published `ConvexOptimization.LogConcaveOn` in its power form $g(x)^a g(y)^{1-a}\le g(ax+(1-a)y)$, which allows zeros (it is not concavity of `Real.log ∘ g`, which would read $\log 0$ as $0$). The highest bidder is chosen with ties broken towards the least index; the paper breaks ties uniformly at random, which only matters on the null event of tied bids (bids are assumed distinct, p. 20). Reserves may be negative (for $\theta\le -B_n$ every $y\ge\theta+B_n$ maximizes the objective with value $0$), which is why the empty inner maximum for $N=1$ is not encoded as $0$. The eigenvalue bounds on $\Sigma$ are not in the theorem's text; they are the hypotheses the proof uses on pp. 57 and 72–73.
-- source:
--   Golrezaei, Javanmard, Mirrokni, Dynamic Incentive-Aware Learning: Robust Pricing in Contextual Auctions, arXiv:2002.11137v1, pp. 11–16, (1), Assumption 1 (p. 12), the auction (pp. 13–14), (4), (10); footnote 12 (p. 20); p. 57 footnote 16; pp. 72–73

import Mathlib
import Definitions.Def_LogConcaveOn

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace IncentiveAwarePricing.CORP

/-- The feature (context) space `ℝ^d` with its Euclidean inner product (p. 11). -/
abbrev Ctx (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-! ### Noise (p. 12) -/

/-- Standing assumptions on the noise (p. 12): `f` is a probability density on `ℝ` which vanishes
outside `[-Bn, Bn]`, is continuous on `[-Bn, Bn]`, and has mean zero. -/
structure NoiseStanding (Bn : ℝ) (f : ℝ → ℝ) : Prop where
  pos : 0 < Bn
  nonneg : ∀ z, 0 ≤ f z
  zero_outside : ∀ z, z ∉ Set.Icc (-Bn) Bn → f z = 0
  continuousOn : ContinuousOn f (Set.Icc (-Bn) Bn)
  mass_one : ∫ z in (-Bn)..Bn, f z = 1
  mean_zero : ∫ z in (-Bn)..Bn, z * f z = 0

/-- The noise distribution function `F(z) = ∫_{(-∞, z]} f` (p. 12; footnote 12, p. 20:
`F(z) = 0` for `z ≤ -Bn` and `F(z) = 1` for `z ≥ Bn`). -/
noncomputable def noiseCDF (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ u in Set.Iic z, f u

/-- The law of one noise term `z_it`: Lebesgue measure with density `f`. -/
noncomputable def noiseLaw (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun z => ENNReal.ofReal (f z))

/-- **Assumption 1** (Log-concavity, p. 12): `F(z)` and `1 - F(z)` are log-concave in
`z ∈ [-Bn, Bn]`. -/
def Assumption1 (Bn : ℝ) (f : ℝ → ℝ) : Prop :=
  ConvexOptimization.LogConcaveOn (Set.Icc (-Bn) Bn) (noiseCDF f) ∧
    ConvexOptimization.LogConcaveOn (Set.Icc (-Bn) Bn) (fun z => 1 - noiseCDF f z)

/-! ### Features (pp. 11–12, 57, 72–73) -/

/-- The feature law `D` is a probability measure supported in the closed unit ball (p. 12). -/
structure FeatureSupport (d : ℕ) (D : Measure (Ctx d)) : Prop where
  isProb : IsProbabilityMeasure D
  norm_le_one : ∀ᵐ x ∂D, ‖x‖ ≤ 1

/-- The feature law `D`, with second-moment matrix `Σ = E[x xᵀ]`, satisfies
`c_min/d · ‖u‖² < uᵀ Σ u ≤ c_max/d · ‖u‖²` for `u ≠ 0` (p. 57 and footnote 16; pp. 72–73). -/
structure FeatureLaw (d : ℕ) (cmin cmax : ℝ) (D : Measure (Ctx d)) : Prop
    extends FeatureSupport d D where
  lower : ∀ u : Ctx d, u ≠ 0 → cmin / d * ‖u‖ ^ 2 < ∫ x, ⟪x, u⟫ ^ 2 ∂D
  upper : ∀ u : Ctx d, ∫ x, ⟪x, u⟫ ^ 2 ∂D ≤ cmax / d * ‖u‖ ^ 2

/-! ### Valuations (1) -/

/-- Valuations (1), p. 12: `v_i = ⟨x, β_i⟩ + z_i`. -/
noncomputable def values {N d : ℕ} (x : Ctx d) (β : Fin N → Ctx d) (z : Fin N → ℝ) : Fin N → ℝ :=
  fun i => ⟪x, β i⟫ + z i

/-! ### Lazy second-price auction with personalized reserves (pp. 13–14) -/

/-- `i` is the highest bidder, ties broken towards the least index. -/
def IsTopBidder {N : ℕ} (b : Fin N → ℝ) (i : Fin N) : Prop :=
  (∀ j, b j ≤ b i) ∧ ∀ j, j < i → b j < b i

/-- `max {r_i, max_{j ≠ i} b_j}`; when `N = 1` the inner maximum is over the empty set (`-∞`) and
the value is `r_i`. -/
noncomputable def thresh {N : ℕ} (b r : Fin N → ℝ) (i : Fin N) : ℝ :=
  (insert (r i) ((Finset.univ.erase i).image b)).max' (Finset.insert_nonempty _ _)

/-- Buyer `i` gets the item in the lazy second-price auction: he is the highest bidder and his bid
clears his own reserve. -/
def LazyWins {N : ℕ} (b r : Fin N → ℝ) (i : Fin N) : Prop :=
  IsTopBidder b i ∧ r i ≤ b i

/-- Allocation `q_i ∈ {0, 1}` of the lazy second-price auction. -/
noncomputable def lazyAlloc {N : ℕ} (b r : Fin N → ℝ) (i : Fin N) : ℝ := by
  classical exact if LazyWins b r i then 1 else 0

/-- Payment of the lazy second-price auction: the winner pays `max {r_i, max_{j ≠ i} b_j}`,
everybody else pays `0`. -/
noncomputable def lazyPay {N : ℕ} (b r : Fin N → ℝ) (i : Fin N) : ℝ := by
  classical exact if LazyWins b r i then thresh b r i else 0

/-- The seller's revenue `∑_i p_i q_i` in one lazy second-price auction. -/
noncomputable def lazyRevenue {N : ℕ} (b r : Fin N → ℝ) : ℝ :=
  ∑ i, lazyPay b r i

/-! ### The optimal-reserve problem (4), (10) -/

/-- The objective `y (1 - F(y - θ))` of (4) and (10), at index `θ = ⟨x, β⟩`. -/
noncomputable def reserveObjective (f : ℝ → ℝ) (θ y : ℝ) : ℝ :=
  y * (1 - noiseCDF f (y - θ))

/-- `res` is a selection of the argmax in (4)/(10): for every index `θ`, `res θ` maximizes
`y ↦ y (1 - F(y - θ))` over all `y ∈ ℝ`. -/
def IsReserveRule (f : ℝ → ℝ) (res : ℝ → ℝ) : Prop :=
  ∀ θ, IsMaxOn (reserveObjective f θ) Set.univ (res θ)

/-! ### Negative log-likelihood terms (9) -/

/-- `-log p` with `-log 0 = +∞` (the `[0, ∞]`-valued negative logarithm). -/
noncomputable def nll (p : ℝ) : ℝ≥0∞ :=
  if p ≤ 0 then ⊤ else ENNReal.ofReal (-Real.log p)

end IncentiveAwarePricing.CORP


