-- Prove2me | Definitions.Def_LeJEPA_Basic
-- name    : LeJEPA_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T10:59:45.921884+00:00
-- url     : https://prove2.me/theorems/487c4720-3971-4fe7-bf86-e1170646d2dc
-- title:
--   LeJEPA: Fisher information, mean-zero densities, covariance, probe bias/variance, characteristic-function distances
-- statement:
--   Objects used by the LeJEPA mission. Throughout, $\mathbb{R}^K$ carries Lebesgue measure.
--
--   1. **Fisher information.** For a differentiable $p:\mathbb{R}^K\to\mathbb{R}$,
--   $$J(p)=\int_{\{p>0\}}\frac{\|\nabla p(x)\|^2}{p(x)}\,dx=\int\|\nabla\log p\|^2\,p\in[0,\infty].$$
--   2. **Mean-zero density.** $p$ is continuously differentiable, $p\ge0$, $\int p=1$, $\int\|x\|^2p(x)\,dx<\infty$ and $\int x\,p(x)\,dx=0$.
--   3. **Covariance.** $\Sigma(p)=\int xx^\top p(x)\,dx$, which is the paper's $\Sigma=\mathbb{E}[XX^\top]$ for a mean-zero $X\sim p$.
--   4. **Gaussian density.** $\mathcal{N}(0,S)$ has density $(2\pi)^{-K/2}(\det S)^{-1/2}\exp(-\tfrac12x^\top S^{-1}x)$.
--   5. **Frobenius norm.** $\|S\|_F=(\sum_{ij}S_{ij}^2)^{1/2}$.
--   6. **Ridge probe bias.** For data $Z\in\mathbb{R}^{N\times K}$, labels $y=Z\beta+\varepsilon$ with $\mathbb{E}\varepsilon=0$, and $\lambda\ge0$, the estimator $\hat\beta=(Z^\top Z+\lambda I)^{-1}Z^\top y$ has bias $\mathbb{E}\hat\beta-\beta=(Z^\top Z+\lambda I)^{-1}Z^\top Z\beta-\beta$.
--   7. **Least-squares total variance.** With $\mathrm{Var}(\varepsilon)=\sigma^2I$, it is $\operatorname{tr}\mathrm{Var}(\hat\beta)=\sigma^2\operatorname{tr}((Z^\top Z)^{-1})$.
--   8. **Moments.** $m_k(P)=\int x^k\,dP$.
--   9. **Characteristic functions.** The standard Gaussian has $\varphi_G(t)=e^{-t^2/2}$, and the empirical characteristic function of samples $z_1,\dots,z_N$ is $\hat\varphi_N(t)=\frac1N\sum_je^{itz_j}$.
--   10. **Characteristic-function distances.** With weight $w_s(t)=e^{-s^2t^2}$,
--   $$\hat D_V(z)=\int w_s(t)\,|\hat\varphi_N(t)-\varphi_G(t)|^2\,dt,\qquad D(P,G)=\int w_s(t)\,|\varphi_P(t)-\varphi_G(t)|^2\,dt.$$
--   These are the statistics of the paper's Appendix B.12–B.13. The Epps–Pulley statistic of Section 4.2.3 is $N\hat D_V$ with $s=1/\sigma$.
--
--   **Formalization Note** Vectors in $\mathbb{R}^K$ are functions $\mathrm{Fin}\,K\to\mathbb{R}$, and gradients are written through partial derivatives. $J(p)$ takes values in $[0,\infty]$, so it is defined without any integrability assumption.
-- source:
--   Balestriero and LeCun, LeJEPA, arXiv:2511.08544v3 (2025), Sections 3.1, 4.2 and Appendices B.1, B.2, B.4, B.12, B.13

import Mathlib

/-!
Balestriero and LeCun, *LeJEPA: Provable and Scalable Self-Supervised Learning Without the Heuristics*,
arXiv:2511.08544v3 (2025). Objects used by the formal statements of the mission.
-/

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace LeJEPA

variable {K N : ℕ}

/-- The `i`-th partial derivative `∂_i p(x)` of `p : ℝ^K → ℝ`. -/
def partialDeriv (p : (Fin K → ℝ) → ℝ) (i : Fin K) (x : Fin K → ℝ) : ℝ :=
  fderiv ℝ p x (Pi.single i 1)

/-- Fisher-information functional `J(p) = ∫ ‖∇ log p‖² p = ∫_{p > 0} ‖∇ p‖² / p`, valued in `[0, ∞]`. -/
def fisherInfo (p : (Fin K → ℝ) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, if 0 < p x then ENNReal.ofReal ((∑ i, partialDeriv p i x ^ 2) / p x) else 0

/-- A mean-zero probability density on `ℝ^K` with finite second moments and continuously differentiable
(the regularity under which the score `∇ log p` and `J(p)` are defined). -/
structure IsMeanZeroDensity (p : (Fin K → ℝ) → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 p
  nonneg : ∀ x, 0 ≤ p x
  integral_eq_one : ∫ x, p x = 1
  integrable_sq : Integrable (fun x => (∑ i, x i ^ 2) * p x)
  mean_zero : ∀ i, ∫ x, x i * p x = 0

/-- Covariance matrix `Σ = E[X Xᵀ]` of a mean-zero density `p`. -/
def covMat (p : (Fin K → ℝ) → ℝ) : Matrix (Fin K) (Fin K) ℝ := fun i j => ∫ x, x i * x j * p x

/-- Density of the Gaussian `N(0, S)` on `ℝ^K`. -/
def gaussDensity (S : Matrix (Fin K) (Fin K) ℝ) (x : Fin K → ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(K : ℝ) / 2) * S.det ^ (-(1 : ℝ) / 2) * Real.exp (-(1 / 2) * (x ⬝ᵥ (S⁻¹ *ᵥ x)))

/-- Frobenius norm `‖S‖_F = (∑_{ij} S_{ij}²)^{1/2}`. -/
def frobNorm (S : Matrix (Fin K) (Fin K) ℝ) : ℝ := Real.sqrt (∑ i, ∑ j, S i j ^ 2)

/-- Bias `E[β̂] - β` of the ridge (Tikhonov) estimator `β̂ = (ZᵀZ + λI)⁻¹ Zᵀ y` when `y = Zβ + ε`, `E[ε] = 0`. -/
def ridgeBias (Z : Matrix (Fin N) (Fin K) ℝ) (lam : ℝ) (β : Fin K → ℝ) : Fin K → ℝ :=
  ((Zᵀ * Z + lam • (1 : Matrix (Fin K) (Fin K) ℝ))⁻¹ * (Zᵀ * Z)) *ᵥ β - β

/-- Total variance `tr Var(β̂) = σ² tr((ZᵀZ)⁻¹)` of the least-squares estimator under noise `Var(ε) = σ² I`. -/
def olsTotalVariance (Z : Matrix (Fin N) (Fin K) ℝ) (σ : ℝ) : ℝ := σ ^ 2 * ((Zᵀ * Z)⁻¹).trace

/-- The `k`-th raw moment `m_k(P) = ∫ x^k dP`. -/
def rawMoment (k : ℕ) (P : Measure ℝ) : ℝ := ∫ x, x ^ k ∂P

/-- Characteristic function of the standard Gaussian, `φ_G(t) = e^{-t²/2}`. -/
def stdGaussCF (t : ℝ) : ℂ := (Real.exp (-(t ^ 2) / 2) : ℂ)

/-- Empirical characteristic function `φ̂_N(t) = (1/N) ∑_j e^{i t z_j}`. -/
def empCF (z : Fin N → ℝ) (t : ℝ) : ℂ := (1 / (N : ℂ)) * ∑ j, Complex.exp (Complex.I * (t : ℂ) * (z j : ℂ))

/-- V-statistic `D̂_V = ∫ w_s(t) |φ̂_N(t) - φ_G(t)|² dt`, Gaussian weight `w_s(t) = e^{-s² t²}`. -/
def ecfDistance (s : ℝ) (z : Fin N → ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-(s ^ 2 * t ^ 2)) * ‖empCF z t - stdGaussCF t‖ ^ 2

/-- Population distance `D(P, G) = ∫ w_s(t) |φ_P(t) - φ_G(t)|² dt`. -/
def cfDistance (s : ℝ) (P : Measure ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-(s ^ 2 * t ^ 2)) * ‖charFun P t - stdGaussCF t‖ ^ 2

end LeJEPA


