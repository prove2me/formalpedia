-- Prove2me | Definitions.Def_ShockWear_RandThreshold_Model
-- name    : ShockWear_RandThreshold_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:31:16.281978+00:00
-- url     : https://prove2.me/theorems/9075d1a6-0993-42b8-9e14-627417a8ff92
-- title:
--   Poisson shock survival function (2.1), convolution powers F^(k), the random-threshold probabilities (5.1) and the classes IHR, IHRA, NBU (p. 631)
-- statement:
--   This file fixes the objects of §5 of Esary, Marshall and Proschan (1973), *Shock models and wear processes*.
--
--   1. **Poisson weights and the shock survival function (2.1).** For $\lambda, t \in \mathbb R$ and $k = 0, 1, \dots$ put $\pi_k(\lambda, t) = e^{-\lambda t}(\lambda t)^k/k!$. Given a sequence $\bar P_0, \bar P_1, \dots$ (the probabilities of surviving $k$ shocks), the survival function of the device is
--   $$\bar H(t) = \sum_{k=0}^\infty \bar P_k\, e^{-\lambda t}\frac{(\lambda t)^k}{k!} \quad (t \ge 0), \qquad \bar H(t) = 1 \quad (t < 0).$$
--   2. **Convolution powers.** For a distribution $F$ on $\mathbb R$, $F^{(0)}$ is degenerate at $0$ and $F^{(k+1)} = F^{(k)} * F$; $F^{(k)}(x)$ is the mass $F^{(k)}$ gives to $(-\infty, x]$, i.e. $P\{X_1 + \cdots + X_k \le x\}$ for independent $X_i \sim F$.
--   3. **Survival function of a law.** For a distribution $G$, $\bar G(x) = 1 - G(x) = G((x, \infty))$.
--   4. **Random-threshold survival probabilities (5.1).** For a damage law $F$ and a threshold law $G$,
--   $$\bar P_k = \int_0^\infty F^{(k)}(x)\, dG(x), \qquad k = 0, 1, \dots,$$
--   i.e. $\bar P_k = P\{X_1 + \cdots + X_k \le Y\}$ with $Y \sim G$ independent of $X_1, X_2, \dots$.
--   5. **Ageing classes (p. 631).** A function $\bar F$ is **IHR** (increasing hazard rate) if $\bar F(x+t)/\bar F(t)$ is decreasing in $t$ whenever $x > 0$; **IHRA** (increasing hazard rate average) if $[\bar F(t)]^{1/t}$ is decreasing in $t > 0$; **NBU** (new better than used) if $\bar F(t + x) \le \bar F(x)\bar F(t)$ for all $x, t \ge 0$. "Decreasing" means non-increasing throughout, as in the paper.
--
--   These are the objects in which the paper's random-threshold results (Theorems 5.1–5.3) and the NBU part (3.5) of Theorem 3.1 are stated.
--
--   **Formalization Note.** A distribution is a measure on $\mathbb R$; the statements that use these definitions assume it is a probability measure and say where it is carried. The integral in (5.1) is taken over all of $\mathbb R$: every statement assumes $G$ is carried by $[0,\infty)$, so this is the paper's $\int_0^\infty$ including a possible atom at $0$. The integrand $x \mapsto F^{(k)}(x)$ is monotone and takes values in $[0,1]$, so the integral is a genuine expectation, never Lean's default value $0$. IHR and NBU are written with the ratios cross-multiplied, which agrees with the paper's ratio form wherever the denominators are positive (the paper restricts variables to avoid zero denominators). $[\bar F(t)]^{1/t}$ is the real power with real exponent $1/t$.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), pp. 628, 631, 636, 642, (2.1), definitions (ii), (iv), (v), (4.1) and (5.1)

import Mathlib

namespace ShockWear.RandThreshold

open MeasureTheory ProbabilityTheory

/-- The Poisson weight $e^{-\lambda t}(\lambda t)^k/k!$. -/
noncomputable def poisW (lam t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-(lam * t)) * (lam * t) ^ k / (k.factorial : ℝ)

/-- (2.1): $\bar H(t) = \sum_k \bar P_k e^{-\lambda t}(\lambda t)^k/k!$ for $t \ge 0$,
and $\bar H(t) = 1$ for $t < 0$. -/
noncomputable def shockSurv (lam : ℝ) (P : ℕ → ℝ) (t : ℝ) : ℝ :=
  if t < 0 then 1 else ∑' k, P k * poisW lam t k

/-- The k-fold convolution $F^{(k)}$ of a law on ℝ; $F^{(0)}$ is degenerate at 0 (p. 636). -/
noncomputable def convPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | k + 1 => Measure.conv (convPow μ k) μ

/-- $F^{(k)}(x)$ = the mass of $(-\infty, x]$ under the k-fold convolution. -/
noncomputable def cdfPow (μ : Measure ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (convPow μ k (Set.Iic x)).toReal

/-- The survival function $\bar G(x) = 1 - G(x) = \nu((x, \infty))$ of a law `ν` on ℝ. -/
noncomputable def survOf (ν : Measure ℝ) (x : ℝ) : ℝ :=
  (ν (Set.Ioi x)).toReal

/-- (5.1): $\bar P_k = \int_0^\infty F^{(k)}(x)\, dG(x)$, the integral taken over ℝ
(the threshold law `ν` is carried by $[0, \infty)$ in every statement that uses it). -/
noncomputable def randP (μ ν : Measure ℝ) (k : ℕ) : ℝ :=
  ∫ x, cdfPow μ k x ∂ν

/-- (ii) IHR: $\bar F(x + t)/\bar F(t)$ is decreasing (non-increasing) in $t$ whenever $x > 0$,
cross-multiplied. -/
def IsIHR (Fb : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → ∀ s t, s ≤ t → Fb (x + t) * Fb s ≤ Fb (x + s) * Fb t

/-- (iv) IHRA: $[\bar F(t)]^{1/t}$ is decreasing (non-increasing) in $t > 0$ (real power). -/
def IsIHRA (Fb : ℝ → ℝ) : Prop :=
  AntitoneOn (fun t => Fb t ^ (1 / t)) (Set.Ioi 0)

/-- (v) NBU: $\bar F(x) \ge \bar F(t + x)/\bar F(t)$ for all $x, t \ge 0$, cross-multiplied. -/
def IsNBU (Fb : ℝ → ℝ) : Prop :=
  ∀ x t, 0 ≤ x → 0 ≤ t → Fb (t + x) ≤ Fb x * Fb t

end ShockWear.RandThreshold


