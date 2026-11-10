-- Prove2me | Definitions.Def_AgnosticImitate_Reduction_Losses
-- name    : AgnosticImitate_Reduction_Losses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:23:19.70903+00:00
-- url     : https://prove2.me/theorems/ba606a93-367a-423d-aa39-93a8bc217aec
-- title:
--   Expected loss, best responses, entropy, divergence, superderivatives, Bregman divergences, natural parametrization, the noise operator and weighted Follow the Leader
-- statement:
--   Definitions 2.1, 2.2, 2.4, 2.7 and Example 2.8 (pp. 14–16, PDF 16–18) and §3.4 (pp. 20–21, PDF 22–23). A loss $\ell:\{\pm1\}\times A\to\mathbb R$ is a function $\ell:\mathbb R\to A\to\mathbb R$ used only at $y=\pm1$.
--
--   - Expected loss `expLoss` $\ell(p,a)=\frac{1+p}2\ell(1,a)+\frac{1-p}2\ell(-1,a)$; best-response function (`IsBestResponse`): $\ell(p,k(p))\le\ell(p,a)$ for all $p\in[-1,1]$ and all $a$; entropy `entropy` $h_\ell(p)=\inf_a\ell(p,a)$; divergence `divergence` $D_\ell(p,a)=\ell(p,a)-h_\ell(p)$; discrete derivative `discDeriv` $\partial\ell(a)=(\ell(1,a)-\ell(-1,a))/2$.
--   - Superderivative on $[\pm1]$ (`IsSuperderivative`): $h(y)\le h(x)+h'(x)(y-x)$ for $x,y\in[-1,1]$. Bregman divergence of a concave $h$ with respect to the chosen superderivative $h'$ (`bregmanConcave`): $D_h(y,x)=D_{-h}(y,x)=h(x)+h'(x)(y-x)-h(y)$ (footnote 7).
--   - Natural parametrization (`IsNaturallyParametrized`): $A=\mathbb R$ and $\partial\ell(\eta)=-\eta$; the class $L_B$ (`IsInLB`) adds a $[\pm B]$-valued best response; `absLossExt` is Example 2.8's $\max(1,|\eta|)-y\eta$.
--   - Noise operator: `noiseExp σ φ v` $=\mathbb E[\varphi(N_\sigma(v))]$, the two-point average over $j\sigma$ and $(j+1)\sigma$, $j=\lfloor v/\sigma\rfloor$, with weights $((j+1)\sigma-v)/\sigma$ and $(v-j\sigma)/\sigma$ (mean-preserving).
--   - Weighted Follow the Leader: `prefixW` $W_t=w_1+\dots+w_t$, `wavg` $\bar p_t=(w_1p_1+\dots+w_tp_t)/W_t$ with $\bar p_0=0$, and `stepDelta` $\delta=\sum_{t=1}^T w_t^2/(W_tW_T)$.
-- source:
--   Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), Agnostic Learning by Imitating, STOC 2027 submission, SHA-256 225d86c2…0fb04, Definitions 2.1, 2.2, 2.4, 2.7, Example 2.8 (pp. 14–16, PDF 16–18), §3.4 (pp. 20–21, PDF 22–23)

import Mathlib

noncomputable section
open Classical

namespace AgnosticImitate.Reduction

/-! # Loss functions, entropy, divergence, Bregman divergences, weighted FTL and smoothing

Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), *Agnostic Learning by
Imitating*, Definitions 2.1, 2.2, 2.4, 2.7 and Example 2.8 (pp. 14–16, PDF 16–18), §3.4
(pp. 20–21, PDF 22–23).

A loss `ℓ : {±1} × A → ℝ` is a function `ℓ : ℝ → A → ℝ` of which only the values at `y = 1` and
`y = -1` are used. -/

/-- Expected loss `ℓ(p, a) = E_{y∼p}[ℓ(y, a)] = (1+p)/2 · ℓ(1, a) + (1-p)/2 · ℓ(-1, a)`
(Definition 2.4); `p ∈ [±1]` is the mean of the label distribution. -/
def expLoss {A : Type*} (ℓ : ℝ → A → ℝ) (p : ℝ) (a : A) : ℝ :=
  (1 + p) / 2 * ℓ 1 a + (1 - p) / 2 * ℓ (-1) a

/-- `k` is a best-response function of `ℓ` (Definition 2.4):
`k(p) ∈ argmin_a ℓ(p, a)` for every `p ∈ [±1]`. -/
def IsBestResponse {A : Type*} (ℓ : ℝ → A → ℝ) (k : ℝ → A) : Prop :=
  ∀ p ∈ Set.Icc (-1 : ℝ) 1, ∀ a : A, expLoss ℓ p (k p) ≤ expLoss ℓ p a

/-- Entropy `h_ℓ(p) = inf_a ℓ(p, a)` (Definition 2.4). -/
def entropy {A : Type*} (ℓ : ℝ → A → ℝ) (p : ℝ) : ℝ :=
  ⨅ a : A, expLoss ℓ p a

/-- Divergence `D_ℓ(p, a) = ℓ(p, a) - h_ℓ(p)` (Definition 2.4). -/
def divergence {A : Type*} (ℓ : ℝ → A → ℝ) (p : ℝ) (a : A) : ℝ :=
  expLoss ℓ p a - entropy ℓ p

/-- The discrete partial derivative `∂ℓ(a) = (ℓ(+1, a) - ℓ(-1, a))/2` (p. 15). -/
def discDeriv {A : Type*} (ℓ : ℝ → A → ℝ) (a : A) : ℝ :=
  (ℓ 1 a - ℓ (-1) a) / 2

/-- `h'` is a superderivative of `h` on `[±1]` (Definition 2.1 with signs flipped):
`h(y) ≤ h(x) + h'(x)(y - x)` for all `x, y ∈ [-1, 1]`. -/
def IsSuperderivative (h h' : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, h y ≤ h x + h' x * (y - x)

/-- Bregman divergence of a concave `h` with respect to a chosen superderivative `h'`
(Definition 2.2 applied to `-h`, `-h'`; footnote 7):
`D_h(y, x) = D_{-h}(y, x) = h(x) + h'(x)(y - x) - h(y)`. -/
def bregmanConcave (h h' : ℝ → ℝ) (y x : ℝ) : ℝ :=
  h x + h' x * (y - x) - h y

/-- Natural parametrization (Definition 2.7): action set `ℝ` and `∂ℓ(η) = -η` for every `η`. -/
def IsNaturallyParametrized (ℓ : ℝ → ℝ → ℝ) : Prop :=
  ∀ η : ℝ, discDeriv ℓ η = -η

/-- The class `L_B` (Definition 2.7): naturally parametrized losses with a `[±B]`-valued
best-response function on `[±1]`. -/
def IsInLB (ℓ : ℝ → ℝ → ℝ) (B : ℝ) : Prop :=
  IsNaturallyParametrized ℓ ∧
    ∃ k : ℝ → ℝ, IsBestResponse ℓ k ∧ ∀ p ∈ Set.Icc (-1 : ℝ) 1, k p ∈ Set.Icc (-B) B

/-- The absolute loss extended to all actions `η ∈ ℝ` (Example 2.8):
`ℓ(y, η) = max(1, |η|) - y η`, which equals `|y - η|` for `y ∈ {±1}` and `η ∈ [±1]`. -/
def absLossExt : ℝ → ℝ → ℝ :=
  fun y η => max 1 |η| - y * η

/-- The expectation `E[φ(N_σ(v))]` of the noise operator of Lemma 3.8: `N_σ(v)` rounds `v` to
`jσ` or `(j+1)σ`, `j = ⌊v/σ⌋`, with probabilities `((j+1)σ - v)/σ` and `(v - jσ)/σ`, so that
its mean is `v` (deterministic at grid points). -/
def noiseExp (σ : ℝ) (φ : ℝ → ℝ) (v : ℝ) : ℝ :=
  let j : ℝ := (⌊v / σ⌋ : ℝ)
  ((j + 1) * σ - v) / σ * φ (j * σ) + (v - j * σ) / σ * φ ((j + 1) * σ)

/-- Prefix sums `W_t = w_1 + ⋯ + w_t` (Lemma 3.4). -/
def prefixW (w : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 t, w s

/-- Weighted averages `p̄_t = (w_1 p_1 + ⋯ + w_t p_t)/W_t`, with `p̄_0 = 0` (Lemma 3.4; Lean's
`x / 0 = 0` also gives `0` whenever `W_t = 0`). -/
def wavg (w p : ℕ → ℝ) (t : ℕ) : ℝ :=
  (∑ s ∈ Finset.Icc 1 t, w s * p s) / prefixW w t

/-- `δ = Σ_{t=1}^T w_t² / (W_t W_T)` (Lemma 3.6). -/
def stepDelta (w : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, w t ^ 2 / (prefixW w t * prefixW w T)

end AgnosticImitate.Reduction


