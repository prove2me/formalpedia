-- Prove2me | Definitions.Def_FreeSamples_FullRevenue_Learning
-- name    : FreeSamples_FullRevenue_Learning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:52:18.605366+00:00
-- url     : https://prove2.me/theorems/098812e0-1690-4f50-b57e-678bf5f52b50
-- title:
--   Buyer and Seller perspectives, posterior process, and Gaussian transition law
-- statement:
--   Let $\theta_0,\mu_b\in\mathbb R$, $v_0>0$, $\sigma_b^2\ge0$, and $n>0$ be the Buyer's prior mean, Seller's mean bias, Buyer prior variance, bias variance, and noise variance. The Buyer prior is $N(\theta_0,v_0)$ and the Seller prior is $N(\theta_0+\mu_b,v_0+\sigma_b^2)$. Both observe $Y_t=\Theta t+\sqrt n B_t$, with Brownian motion independent of $\Theta$. The published primitive posterior maps compute the Buyer mean $m_t$, Buyer variance $v_t$, Seller variance $w_t$, and mean difference $g_t$.
--
--   At a current Buyer state $(m,v)$, an observer whose conditional state law is $N(m+g,w)$ sees the next Buyer mean, after $h\ge0$ additional samples, with Gaussian law
--   $$K_h=N\left(m+\frac{vg h}{vh+n},\frac{v^2(nh+wh^2)}{(vh+n)^2}\right).$$
--   The Buyer perspective uses $(w,g)=(v_t,0)$; the Seller uses $(w_t,g_t)$. The kernel at $h=0$ is the point mass at $m$. The layer also names the exact squared-increment formula and an $h$-independent remainder coefficient used in Lemma 1(iii). It assumes no moment or generator identities; the theorem items assert the conditional identities.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, pinned local PDF snapshot (creation metadata 2021-08-30; SHA-256 2e29ad6e37639d93e587e9999f63959d3eb52c66a1fe2ac7e78f3d33976e44c0), pp.9–10, §§2.2–2.3; pp.13–14, Proposition 1, Eq.(2), Lemma 1; p.29, proof of Lemma 1

import Definitions.Def_FreeSamples_Revenue_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.FullRevenue

/-- The two perspectives in Proposition 1 and Lemma 1. -/
inductive Perspective where
  | buyer
  | seller

/-- Mean of the indicated prior. -/
def priorMean (p : Revenue.Params) (i : Perspective) : ℝ :=
  match i with
  | .buyer => p.θ₀
  | .seller => p.θ₀ + p.μb

/-- Variance of the indicated prior; the seller's includes the bias variance. -/
def priorVariance (p : Revenue.Params) (i : Perspective) : ℝ :=
  match i with
  | .buyer => p.σ₀sq
  | .seller => p.σssq

/-- Posterior variance of the indicated perspective. -/
noncomputable def currentVariance (p : Revenue.Params) (i : Perspective) (t : ℝ) : ℝ :=
  match i with
  | .buyer => p.buyerVar t
  | .seller => p.sellerVar t

/-- Posterior mean displacement from the buyer's mean. -/
noncomputable def currentGap (p : Revenue.Params) (i : Perspective) (t y : ℝ) : ℝ :=
  match i with
  | .buyer => 0
  | .seller => p.gMis t y

/-- The actual buyer posterior process, computed from the observed signal. -/
noncomputable def posteriorMean (p : Revenue.Params) {Ω : Type*} (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  p.buyerMean t (Revenue.Y p.σsq θ B t ω)

/-- Gaussian conditional law of the next buyer mean, given the present mean m,
variance v, and the observer's latent-state mean m+g and variance w.
At h=0 this is the point mass at m. Only h≥0,v>0,n>0,w≥0 are used. -/
noncomputable def transitionLaw (n m v w g h : ℝ) : Measure ℝ :=
  Revenue.N (m + Revenue.postVar n v h / n * g * h)
    ((Revenue.postVar n v h / n) ^ 2 * (n * h + w * h ^ 2))

/-- Exact conditional squared increment from the Gaussian calculation on p.29. -/
noncomputable def secondMoment (v w g n h : ℝ) : ℝ :=
  v ^ 2 * (n * h + (w + g ^ 2) * h ^ 2) / (v * h + n) ^ 2

/-- An h-independent remainder coefficient for 0<h≤1. -/
noncomputable def remainderConstant (v w g n : ℝ) : ℝ :=
  v ^ 2 / n ^ 2 * (w + g ^ 2 + 2 * v + v ^ 2 / n)

end FreeSamples.FullRevenue


