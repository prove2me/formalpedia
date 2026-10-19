-- Prove2me | Definitions.Def_SOSInference_Means_tauLaw
-- name    : SOSInference_Means_tauLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:51.453226+00:00
-- url     : https://prove2.me/theorems/b1b00977-0318-4a11-bca5-050c4f9661ec
-- title:
--   Theorem 1 limit objects — $\Lambda(x,\lambda)$, the law of $\tau(\lambda)$, $\tilde g$, $\tilde\eta$, $\rho$, $c_0$ and the limit maps $\varphi_1,\varphi_2,\varphi_l$
-- statement:
--   Fix a model with densities $f_X,f_Y$ and ratio $\kappa$ in dimension $l$, and let $\mu_X$ be the law with density $f_X$.
--
--   1. The **rate** is $\displaystyle\Lambda(x,\lambda)=\big[f_X(x+\lambda/2)+\kappa f_Y(x+\lambda/2)\big]\frac{\pi^{l/2}}{\Gamma(l/2+1)}$ for $x,\lambda\in\mathbb R^l$.
--   2. $\tau(\lambda)$ is the mixture of exponentials: conditionally on $X_1=x$ it is exponential with rate $\Lambda(x,\lambda)$, so $\mathbb P[\tau(\lambda)>t]=\mathbb E[\exp(-\Lambda(X_1,\lambda)t)]$. For $l=2$, $\pi^{l/2}/\Gamma(l/2+1)=\pi$, so $\tau(0)$ is the variable $\tau$ of Theorem 1 with $\mathbb P(\tau>t)=\mathbb E[\exp(-(f_X(X_1)+\kappa f_Y(X_1))\pi t)]$.
--   3. $\tilde g(x)=\mathbb P\big(\tau(0)\le\|x\|_2^2\big)$ and $\tilde\eta(x)=\mathbb E\big[\max\big(1-\tau(0)/\|x\|_2^2,\,0\big)\big]$.
--   4. For $z\ne 0$, $\rho(z)$ is the solution $\rho>0$ of $1/\rho=\tilde g(\rho z)$ (defined as the infimum of the solution set; that the solution exists and is unique is equation (31), a milestone), and $\rho(0)=0$.
--   5. $c_0=\mathbb E\Big[\dfrac{\pi^{l/2}}{\Gamma(l/2+1)}\big(f_X(X_1)+\kappa f_Y(X_1)\big)\Big]=\mathbb E[\Lambda(X_1,0)]$.
--   6. The limit maps $\mathbb R^l\to\mathbb R$:
--   $$\varphi_1(z)=\|z\|_2^2,\qquad \varphi_2(z)=\rho(z)\big(2-\tilde\eta(\rho(z)z)\,\rho(z)\big)\|z\|_2^2,\qquad \varphi_l(z)=\frac{2l+2}{l+2}\cdot\frac{\|z\|_2^{1+1/(l+1)}}{c_0^{1/(l+1)}} .$$
--
--   With $\tilde Z\sim N(0,\mathrm{Var}(X))$, the limit laws of Theorem 1 are those of $\varphi_1(\tilde Z)$ ($l=1$), $\varphi_2(\tilde Z)$ ($l=2$) and $\varphi_l(\tilde Z)$ ($l\ge3$).
--
--   **Formalization Note** $\tilde g$, $\tilde\eta$ and $\rho$ are defined from the law of $\tau(0)$ and the fixed-point property exactly as printed, never by closed forms. Theorem 1 prints the $l=2$ limit with $\tilde\eta(\tilde Z)$; $\varphi_2$ uses $\tilde\eta(\rho(\tilde Z)\tilde Z)$, which is what the derivation on p. 45 yields (see the goal theorem). At $x=0$ the expression $\tilde\eta(0)$ is undefined in the paper; Lean's convention $t/0=0$ gives $\tilde\eta(0)=1$, a value never used.
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, pp. 15–16, Theorem 1; p. 40, Λ(X_i, λ) and τ(λ); p. 45, (31); p. 47, C

import Mathlib
import Definitions.Def_SOSInference_Means_Model

/-!
# Sample out-of-sample inference: the limit objects of Theorem 1

Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4,
pp. 15–16, Theorem 1 (`g̃`, `η̃`, `ρ`, `τ`, the three limits); p. 40, `Λ(X_i, λ)` and `τ(λ)`;
p. 47, the constant `C`.
-/

namespace SOSInference.Means

noncomputable section

open MeasureTheory ProbabilityTheory

/-- The law `μ_X` of `X_1`: the probability measure with density `f_X`. -/
def lawX {l : ℕ} (M : Model l) : Measure (E l) := lawOfDensity M.fX

/-- The Poisson rate (p. 40)
`Λ(x, λ) = [f_X(x + λ/2) + κ f_Y(x + λ/2)] π^{l/2} / Γ(l/2 + 1)`. -/
def Lam {l : ℕ} (M : Model l) (x lam : E l) : ℝ :=
  (M.fX (x + (1 / 2 : ℝ) • lam) + M.κ * M.fY (x + (1 / 2 : ℝ) • lam)) *
    Real.pi ^ ((l : ℝ) / 2) / Real.Gamma ((l : ℝ) / 2 + 1)

/-- The law of `τ(λ)` (p. 40): conditionally on `X_1 = x`, `τ(λ)` is exponential with rate
`Λ(x, λ)`, so `P[τ(λ) > t] = E[exp(−Λ(X_1, λ) t)]`. Encoded as the mixture
`∫ Exp(Λ(x, λ)) μ_X(dx)`. For `l = 2`, `π^{l/2}/Γ(l/2 + 1) = π`, so `τ(0)` is the `τ` of
Theorem 1 (p. 15): `P(τ > t) = E[exp(−(f_X(X_1) + κ f_Y(X_1)) π t)]`. -/
def tauLaw {l : ℕ} (M : Model l) (lam : E l) : Measure ℝ :=
  (lawX M).bind (fun x => expMeasure (Lam M x lam))

/-- `g̃(x) = P(τ(0) ≤ ‖x‖₂²)` (Theorem 1, p. 15). -/
def gtilde {l : ℕ} (M : Model l) (x : E l) : ℝ :=
  ((tauLaw M 0) (Set.Iic (‖x‖ ^ 2))).toReal

/-- `η̃(x) = E[max(1 − τ(0)/‖x‖₂², 0)]` (Theorem 1, p. 16).

**Formalization Note.** At `x = 0` the paper's expression is undefined; Lean's `t / 0 = 0`
gives `η̃(0) = 1`. The value at `0` is never used (`η̃` is evaluated at `ρ(z) z` with `z ≠ 0`,
`ρ(z) > 0`). -/
def etatilde {l : ℕ} (M : Model l) (x : E l) : ℝ :=
  ∫ t, max (1 - t / ‖x‖ ^ 2) 0 ∂(tauLaw M 0)

/-- `ρ(z)`: the solution `ρ > 0` of `1/ρ = g̃(ρ z)` (Theorem 1, p. 15; (31), p. 45), defined by
this property (as the infimum of the solution set; milestone (31) asserts that the solution
exists and is unique for `z ≠ 0`).

**Formalization Note.** At `z = 0` the equation reads `1/ρ = P(τ(0) ≤ 0) = 0` and has no solution;
`ρ(0) := 0`. The Gaussian limit `Z̃` has a nondegenerate covariance, so `{Z̃ = 0}` is a null event. -/
def rho {l : ℕ} (M : Model l) (z : E l) : ℝ :=
  if z = 0 then 0 else sInf {r : ℝ | 0 < r ∧ 1 / r = gtilde M (r • z)}

/-- The constant `c₀ = E[π^{l/2}/Γ(l/2 + 1) (f_X(X_1) + κ f_Y(X_1))]` of the `l ≥ 3` limit
(Theorem 1, p. 16; `C` on p. 47), i.e. `E[Λ(X_1, 0)]`. -/
def c0 {l : ℕ} (M : Model l) : ℝ :=
  ∫ x, Lam M x 0 ∂(lawX M)

/-- The `l = 1` limit map `φ₁(z) = ‖z‖₂²`: for `Z̃ ~ N(0, σ²)`, `φ₁(Z̃) ~ σ²χ²₁`. -/
def phi1 {l : ℕ} (z : E l) : ℝ := ‖z‖ ^ 2

/-- The `l = 2` limit map `φ₂(z) = ρ(z) (2 − η̃(ρ(z) z) ρ(z)) ‖z‖₂²`.

**Formalization Note.** Theorem 1 (p. 15) prints `η̃(Z̃)`; the derivation on p. 45
(`G(ζ, n) = ‖ζ‖²η̃(ζ) + o(1)` at the maximizer `ζ*_n = −ρ Z_n`) gives `η̃(ρ Z̃)`, which is used here. -/
def phi2 {l : ℕ} (M : Model l) (z : E l) : ℝ :=
  rho M z * (2 - etatilde M (rho M z • z) * rho M z) * ‖z‖ ^ 2

/-- The `l ≥ 3` limit map
`φ_l(z) = (2l + 2)/(l + 2) · ‖z‖₂^{1 + 1/(l+1)} / c₀^{1/(l+1)}` (Theorem 1, p. 16). -/
def phi3 {l : ℕ} (M : Model l) (z : E l) : ℝ :=
  (2 * (l : ℝ) + 2) / ((l : ℝ) + 2) * ‖z‖ ^ (1 + 1 / ((l : ℝ) + 1)) /
    (c0 M) ^ (1 / ((l : ℝ) + 1))

end

end SOSInference.Means


