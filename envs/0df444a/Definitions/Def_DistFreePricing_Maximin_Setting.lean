-- Prove2me | Definitions.Def_DistFreePricing_Maximin_Setting
-- name    : DistFreePricing_Maximin_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:50.41936+00:00
-- url     : https://prove2.me/theorems/254d8f83-7eb9-4d5e-8a02-c659dca31315
-- title:
--   §3, pp. 8–11 — the mean–variance class 𝓕, posted-price profit π(p;F), τ, γ, k*, p*, L, U, ρ, φ and the two-point laws
-- statement:
--   The model of Chen, Hu and Perakis, *Distribution-Free Pricing* (§3, pp. 8–9; Theorems 1–2, pp. 10–11; proof of Theorem 1(b), OA p. 11).
--
--   A seller posts a price $p\in\mathbb R$ for a product with constant marginal cost $c$. The valuation $V\ge 0$ of a randomly selected customer has law $F$, and the customer buys whenever $V\ge p$. The **profit** of price $p$ against $F$ is
--
--   $$\pi(p;F)=(p-c)\,\mathbb P_F(V\ge p).$$
--
--   Given a mean $\mu$ and a standard deviation $\sigma$, the **ambiguity class** $\mathscr F$ is the set of all probability laws $F$ on $\mathbb R$ with $F((-\infty,0))=0$ (nonnegative support), finite first and second moments, $\mathbb E_F[V]=\mu$ and $\mathbb E_F[V^2]=\mu^2+\sigma^2$.
--
--   The paper's primitives are the ratios
--   $$\tau=\frac{\mu-c}{\sigma},\qquad \gamma=\frac{c}{\mu},$$
--   the **safety factor** (the real root of Cardano's cubic)
--   $$k^*(\tau)=\sqrt[3]{\tau+\sqrt{\tau^2+1}}+\sqrt[3]{\tau-\sqrt{\tau^2+1}},$$
--   the **robust price** $p^*=\mu-k^*\sigma$, the lower and upper profit bounds
--   $$L=(\mu-c)\Big(1-\frac{3}{2\tau}k^*\Big),\qquad U=\mu-\frac{\tau^2}{1+\tau^2}\,c,$$
--   the **performance guarantee**
--   $$\rho=\frac{1-\frac{3}{2\tau}k^*}{1+\frac{\gamma}{(1-\gamma)(1+\tau^2)}},$$
--   the auxiliary function $\varphi(k)=\big(1-\tfrac{k}{\tau}\big)\big(1-\tfrac{1}{1+k^2}\big)$ (the paper writes $k\sigma/(\mu-c)$ for $k/\tau$), and, for $k\ne 0$, the **two-point law** placing mass $1/(1+k^2)$ at $\mu-k\sigma$ and mass $1-1/(1+k^2)$ at $\mu+\sigma/k$.
--
--   These objects carry every statement of the mission: Theorem 1 bounds $\pi(p^*;F)$ and $\max_p\pi(p;F)$ over $\mathscr F$ by $L$ and $U$, and Theorem 2 shows that $p^*$ is the maximin price and earns at least the fraction $\rho$ of the best profit.
--
--   **Formalization Note** Laws are measures on $\mathbb R$; $\mathscr F$ requires `IsProbabilityMeasure`, $F(\text{Iio }0)=0$, integrability of $v$ and $v^2$ (the paper's "finite first and second moments", p. 8) and the two moment identities. The profit uses the closed ray $[p,\infty)$, matching $\mathbb P(V\ge p)=1-\lim_{v\to p^-}F(v)$. Because $\tau-\sqrt{\tau^2+1}<0$ and Lean's real power of a negative base is not the real cube root, $k^*$ is written with two positive bases, $k^*=(\sqrt{\tau^2+1}+\tau)^{1/3}-(\sqrt{\tau^2+1}-\tau)^{1/3}$; this is the printed formula because the real cube root is odd. All quantities are real-valued with Lean's convention $x/0=0$; the theorems add the hypotheses ($\sigma>0$, $c<\mu$ where $\rho$ is used) under which no division by zero occurs.
-- source:
--   Chen, Hu, Perakis, Distribution-Free Pricing, accepted manuscript (MSOM, doi:10.1287/msom.2021.1055), §3 (pp. 8–9), Theorems 1–2 (pp. 10–11), proof of Theorem 1(b) (OA p. 11)

import Mathlib

namespace DistFreePricing.Maximin

open MeasureTheory

/-- The class 𝓕 (Chen–Hu–Perakis, §3, p. 9): probability laws `F` of the valuation `V` on `ℝ`,
supported on `[0, ∞)` (`F (Iio 0) = 0`), with finite first and second moments (integrability of
`v` and `v²`), mean `μ` and second moment `μ² + σ²` (so standard deviation `σ`). -/
def valClass (μ σ : ℝ) : Set (Measure ℝ) :=
  {F | IsProbabilityMeasure F ∧ F (Set.Iio 0) = 0 ∧
    Integrable (fun v : ℝ => v) F ∧ Integrable (fun v : ℝ => v ^ 2) F ∧
    ∫ v, v ∂F = μ ∧ ∫ v, v ^ 2 ∂F = μ ^ 2 + σ ^ 2}

/-- The posted-price profit `π(p;F) = (p − c) P(V ≥ p)` (p. 8), with the closed ray `[p, ∞)`. -/
noncomputable def profit (c p : ℝ) (F : Measure ℝ) : ℝ :=
  (p - c) * (F (Set.Ici p)).toReal

/-- `τ = (μ − c)/σ` (p. 9). -/
noncomputable def tau (c μ σ : ℝ) : ℝ := (μ - c) / σ

/-- `γ = c/μ` (p. 9). -/
noncomputable def gam (c μ : ℝ) : ℝ := c / μ

/-- The safety factor `k* = ∛(t + √(t²+1)) + ∛(t − √(t²+1))` (Theorem 1(b), p. 10), written with
two positive bases: `t − √(t²+1) < 0`, `Real.rpow` of a negative base is not the real cube root,
and the real cube root is odd, so `∛(t − √(t²+1)) = −(√(t²+1) − t)^{1/3}`. -/
noncomputable def kStar (t : ℝ) : ℝ :=
  (Real.sqrt (t ^ 2 + 1) + t) ^ ((1 : ℝ) / 3) - (Real.sqrt (t ^ 2 + 1) - t) ^ ((1 : ℝ) / 3)

/-- The optimal robust price `p* = μ − k* σ` with `k* = k*(τ)` (Theorem 2, p. 11). -/
noncomputable def pStar (c μ σ : ℝ) : ℝ := μ - kStar (tau c μ σ) * σ

/-- The lower bound `L = (μ − c)(1 − 3k*/(2τ))` (Theorem 1(b), p. 10). -/
noncomputable def lowerL (c μ σ : ℝ) : ℝ :=
  (μ - c) * (1 - 3 / (2 * tau c μ σ) * kStar (tau c μ σ))

/-- The upper bound `U = μ − τ²/(1 + τ²) · c` (Theorem 1(a), p. 10). -/
noncomputable def upperU (c μ σ : ℝ) : ℝ :=
  μ - (tau c μ σ) ^ 2 / (1 + (tau c μ σ) ^ 2) * c

/-- The performance guarantee `ρ = (1 − 3k*/(2τ)) / (1 + γ/((1 − γ)(1 + τ²)))` (Theorem 2, p. 11). -/
noncomputable def rho (c μ σ : ℝ) : ℝ :=
  (1 - 3 / (2 * tau c μ σ) * kStar (tau c μ σ)) /
    (1 + gam c μ / ((1 - gam c μ) * (1 + (tau c μ σ) ^ 2)))

/-- `φ(k) = (1 − k/τ)(1 − 1/(1 + k²))` (proof of Theorem 1(b), OA p. 11), where the printed
`kσ/(μ − c)` is `k/τ`; the first argument is `τ`. -/
noncomputable def phi (t k : ℝ) : ℝ := (1 - k / t) * (1 - 1 / (1 + k ^ 2))

/-- The two-point law of Theorem 1(b) (p. 10): `μ − kσ` with probability `1/(1 + k²)` and
`μ + σ/k` with probability `1 − 1/(1 + k²)`. -/
noncomputable def twoPoint (μ σ k : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / (1 + k ^ 2)) • Measure.dirac (μ - k * σ) +
    ENNReal.ofReal (1 - 1 / (1 + k ^ 2)) • Measure.dirac (μ + σ / k)

end DistFreePricing.Maximin


