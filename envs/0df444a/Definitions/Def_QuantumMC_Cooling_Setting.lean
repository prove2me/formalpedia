-- Prove2me | Definitions.Def_QuantumMC_Cooling_Setting
-- name    : QuantumMC_Cooling_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:01.206001+00:00
-- url     : https://prove2.me/theorems/21914937-3d2a-409b-b3e6-41e06484f109
-- title:
--   §1.3, §3–3.2, pp. 5–6, 14–16 — partition function Z(β), Gibbs distributions π_i, Y_i, α_i, Chebyshev cooling schedules (Definition 1), χ², quantum samples |π⟩
-- statement:
--   Let $\Omega$ be a finite set of configurations and $H:\Omega\to\{0,1,2,\dots\}$ a Hamiltonian with nonnegative integer values. Inverse temperatures range over $[0,\infty]$.
--
--   1. **Boltzmann weight.** For $\beta\in[0,\infty)$ and $h\in\mathbb N$, the weight is $e^{-\beta h}$; at $\beta=\infty$ it is $1$ if $h=0$ and $0$ otherwise (the convention $0^0=1$, under which $Z(\infty)$ counts the configurations with $H(x)=0$).
--   2. **Partition function.** $$Z(\beta)=\sum_{x\in\Omega}e^{-\beta H(x)}.$$
--   3. **Gibbs distribution.** $\pi_\beta(x)=e^{-\beta H(x)}/Z(\beta)$; along a sequence of inverse temperatures $\beta_0,\beta_1,\dots$ one writes $\pi_i=\pi_{\beta_i}$.
--   4. **Ratios and estimators.** $\alpha_i=Z(\beta_{i+1})/Z(\beta_i)$ and the random variable $Y_i(x)=e^{-(\beta_{i+1}-\beta_i)H(x)}$.
--   5. **Cooling schedule.** A sequence with $0=\beta_0<\beta_1<\dots<\beta_\ell=\infty$.
--   6. **$B$-Chebyshev cooling schedule** (Definition 1). A cooling schedule such that for all $i=0,\dots,\ell-1$
--   $$\frac{Z(2\beta_{i+1}-\beta_i)\,Z(\beta_i)}{Z(\beta_{i+1})^2}\le B.$$
--   7. **Chi-squared divergence.** For functions $\nu,\pi$ on $\Omega$, $$\chi^2(\nu,\pi)=\sum_{x\in\Omega}\pi(x)\Big(\frac{\nu(x)}{\pi(x)}-1\Big)^2.$$
--   8. **Quantum sample.** The vector $|\pi\rangle=\sum_{x\in\Omega}\sqrt{\pi(x)}\,|x\rangle$ in $\ell^2(\Omega;\mathbb C)$.
--
--   These are the objects of the partition-function part of the paper: the telescoping-product estimator of $Z(\infty)$ and the overlap bound between consecutive quantum samples are both stated in terms of them.
--
--   **Formalization Note** Inverse temperatures live in $[0,\infty]$ (`ℝ≥0∞`), so $\beta_\ell=\infty$ is exact; the weight branches on $\beta=\infty$ instead of evaluating $e^{-\infty\cdot h}$ through a real number. The differences $\beta_{i+1}-\beta_i$ and $2\beta_{i+1}-\beta_i$ are truncated subtractions in $[0,\infty]$, which are exact on a cooling schedule because $\beta_i<\beta_{i+1}$ and $\infty-b=\infty$ for finite $b$. In Lean a division by zero returns $0$; every theorem that divides by $Z(\beta)$ or by $\pi(x)$ carries a hypothesis making the denominator positive. A schedule is a function $\mathbb N\to[0,\infty]$ of which only $\beta_0,\dots,\beta_\ell$ matter. $\sqrt{\cdot}$ is the real square root.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §1.3 pp. 5–6 (|π⟩, Z(∞)), §3 p. 14 (Z, π_i, α_i), §3.1 pp. 14–15 (Y_i, Definition 1), §3.2 p. 16 (χ²), p. 20 (0⁰ = 1)

import Mathlib

namespace QuantumMC.Cooling

open scoped ENNReal

variable {Ω : Type*} [Fintype Ω]

/-- The Boltzmann weight `e^{-β h}` at inverse temperature `β ∈ [0, ∞]` and energy `h ∈ ℕ`.
At `β = ∞` it is `1` if `h = 0` and `0` otherwise, so that `Z(∞)` counts the configurations
with `H(x) = 0` (Montanaro, arXiv:1504.06987v3, §1.3, p. 5; convention `0⁰ = 1`, p. 20). -/
noncomputable def weight (β : ℝ≥0∞) (h : ℕ) : ℝ :=
  if β = ⊤ then (if h = 0 then 1 else 0) else Real.exp (-(β.toReal * h))

/-- The partition function `Z(β) = ∑_{x ∈ Ω} e^{-β H(x)}` (§3, p. 14). -/
noncomputable def Z (H : Ω → ℕ) (β : ℝ≥0∞) : ℝ :=
  ∑ x, weight β (H x)

/-- The Gibbs distribution `π_β(x) = e^{-β H(x)} / Z(β)` (§3, p. 14);
`π_i = gibbs H (β i)`. -/
noncomputable def gibbs (H : Ω → ℕ) (β : ℝ≥0∞) (x : Ω) : ℝ :=
  weight β (H x) / Z H β

/-- The ratio `α_i = Z(β_{i+1}) / Z(β_i)` (§3, p. 14). -/
noncomputable def alpha (H : Ω → ℕ) (β : ℕ → ℝ≥0∞) (i : ℕ) : ℝ :=
  Z H (β (i + 1)) / Z H (β i)

/-- The random variable `Y_i(x) = e^{-(β_{i+1} - β_i) H(x)}` (§3.1, p. 14). The subtraction in
`ℝ≥0∞` is exact along a cooling schedule, where `β_i < β_{i+1}`. -/
noncomputable def Y (H : Ω → ℕ) (β : ℕ → ℝ≥0∞) (i : ℕ) (x : Ω) : ℝ :=
  weight (β (i + 1) - β i) (H x)

/-- A cooling schedule `0 = β_0 < β_1 < ⋯ < β_ℓ = ∞` (§3, p. 14). Only `β 0, …, β ℓ` matter. -/
def IsCoolingSchedule (β : ℕ → ℝ≥0∞) (ℓ : ℕ) : Prop :=
  β 0 = 0 ∧ (∀ i < ℓ, β i < β (i + 1)) ∧ β ℓ = ⊤

/-- Definition 1 (p. 15): `β_0, …, β_ℓ` is a `B`-Chebyshev cooling schedule for `Z` if it is a
cooling schedule and `Z(2β_{i+1} - β_i) Z(β_i) / Z(β_{i+1})² ≤ B` for all `i = 0, …, ℓ - 1`. -/
def IsChebyshevSchedule (H : Ω → ℕ) (β : ℕ → ℝ≥0∞) (ℓ : ℕ) (B : ℝ) : Prop :=
  IsCoolingSchedule β ℓ ∧
    ∀ i < ℓ, Z H (2 * β (i + 1) - β i) * Z H (β i) / Z H (β (i + 1)) ^ 2 ≤ B

/-- The chi-squared divergence `χ²(ν, π) = ∑_{x ∈ Ω} π(x) (ν(x)/π(x) - 1)²` (§3.2, p. 16). -/
noncomputable def chiSq (ν π : Ω → ℝ) : ℝ :=
  ∑ x, π x * (ν x / π x - 1) ^ 2

/-- The coherent quantum sample state `|π⟩ = ∑_{x ∈ Ω} √π(x) |x⟩` (§1.3, p. 6), as a vector of
`EuclideanSpace ℂ Ω = ℓ²(Ω; ℂ)` with real amplitudes `√π(x)`. -/
noncomputable def qsample (π : Ω → ℝ) : EuclideanSpace ℂ Ω :=
  WithLp.toLp 2 (fun x => ((Real.sqrt (π x) : ℝ) : ℂ))

end QuantumMC.Cooling


