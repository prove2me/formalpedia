-- Prove2me | Definitions.Def_TerminalRank_Equilibrium_Model
-- name    : TerminalRank_Equilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:30.320811+00:00
-- url     : https://prove2.me/theorems/2422e31e-2f88-4a89-908f-ba942070485c
-- title:
--   §2–§3, pp. 3–8, (2.3), (2.7), Proposition 2.1, (3.2)–(3.3) — reward classes, the weak-form control problem V(R, µ̃), equilibrium, f0, β, quantile, g
-- statement:
--   The model of the rank-based terminal tournament of Bayraktar and Zhang.
--
--   **Data.** A time horizon $T>0$, a cost coefficient $c>0$, a volatility $\sigma>0$ and an initial project value $x_0\in\mathbb R$. A probability space $(\Omega,\mathcal F,P)$ carries a real Brownian motion $(B_t)_{t\ge0}$ under $P$, and the terminal project value under zero effort is
--   $$X_T := x_0+\sigma B_T .$$
--
--   **Rewards.** A reward $R(x,r,m)$ depends on the player's own terminal value $x$, her rank $r\in[0,1]$ in the population, and the population mean $m$. The class $\mathcal R_b$ consists of the bounded rewards that are weakly increasing in each argument (ranks $r\in[0,1]$ only). The class $\mathcal R^{rm}_b$ consists of bounded rewards $R(r,m)$ that do not depend on $x$, are weakly increasing in $r\in[0,1]$ and in $m$, and are continuous in $m$; such a reward is regarded as an element of $\mathcal R_b$ through $\mathrm{lift}(R)(x,r,m)=R(r,m)$.
--
--   For a probability measure $\mu$ on $\mathbb R$ with c.d.f. $F_\mu$ and mean $m_\mu=\int y\,d\mu(y)$, write $R_\mu(x):=R(x,F_\mu(x),m_\mu)$.
--
--   **Control problem (2.3).** The admissible set $\mathcal Q$ consists of the probability measures $Q\sim P$. Given the population law $\tilde\mu$, the single player's value is
--   $$V(R,\tilde\mu):=\sup_{Q\in\mathcal Q}\ E^Q\big[R_{\tilde\mu}(X_T)\big]-2c\sigma^2H(Q\,|\,P),$$
--   with $H$ the relative entropy. $Q$ is *optimal* if it attains this supremum.
--
--   **Equilibrium (p. 7).** A probability law $\mu$ with a finite first moment is an equilibrium if it is a fixed point of the best response: there is an optimal $Q$ for $V(R,\mu)$ whose law of $X_T$ is $\mu$.
--
--   **Explicit objects.** With $\varphi$ the standard normal density, $N$ the standard normal c.d.f.,
--   $$f_0(x)=\frac{1}{\sigma\sqrt T}\varphi\Big(\frac{x-x_0}{\sigma\sqrt T}\Big),\qquad \beta(\tilde\mu)=\int_{\mathbb R}f_0(y)\exp\Big(\frac{R_{\tilde\mu}(y)}{2c\sigma^2}\Big)dy,$$
--   the quantile function $q_\mu(r)=\inf\{x: r\le F_\mu(x)\}$, $N^{-1}=q_{\mathcal N(0,1)}$, the ratio
--   $$y_m(r)=\frac{\int_0^r\exp(-R(z,m)/2c\sigma^2)\,dz}{\int_0^1\exp(-R(z,m)/2c\sigma^2)\,dz},$$
--   and the map $g(m)=x_0+\sigma\sqrt T\int_0^1N^{-1}(y_m(r))\,dr$ of (3.3).
--
--   These objects carry every statement of the mission: the value and the equilibrium are defined from the path-space problem (2.3), never from the closed forms that the theorems derive.
--
--   **Formalization Note.** The rewards are real-valued and bounded in the stated classes; every class condition is imposed only for ranks $r\in[0,1]$, the only ranks that occur. The sample space $\Omega$ is arbitrary with `IsBrownianReal B P`; this is the paper's Wiener space up to relabelling, and Remark 2.1's larger filtration. The supremum in $V$ runs over $Q\sim P$ with $H(Q|P)<\infty$ (relative entropy is Mathlib's `klDiv`, valued in $[0,\infty]$); the excluded $Q$ have objective $-\infty$ in the paper, so the value is unchanged, and the set is nonempty ($Q=P$) and bounded above by $\sup|R|$. $\mathcal N(x_0,\sigma^2T)$ is `normalLaw`. The mean $m_\mu$ is the Bochner integral, which is $0$ when $\mu$ has no first moment. Equilibrium explicitly requires a finite first moment, as the paper's $R_\mu$ uses it.
-- source:
--   Bayraktar & Zhang, Terminal Ranking Games, arXiv:1906.09628v2, pp. 3–8, §2–§3: reward classes p. 3 and p. 7, (2.3) p. 4, (2.7) and Proposition 2.1 p. 5, equilibrium p. 7, (3.2)–(3.3) pp. 7–8

import Mathlib

namespace TerminalRank.Equilibrium

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The class `ℛ_b` of bounded reward functions (Bayraktar–Zhang, arXiv:1906.09628v2, p. 3).
A reward `R(x, r, m)` (own terminal value `x`, rank `r ∈ [0, 1]`, population mean `m`) is weakly
increasing in each argument (footnote 1, p. 3) and bounded. Only ranks `r ∈ [0, 1]` are ever
used, so every condition is imposed on `r ∈ [0, 1]` only. -/
def IsBddReward (R : ℝ → ℝ → ℝ → ℝ) : Prop :=
  (∀ r ∈ Set.Icc (0 : ℝ) 1, ∀ m : ℝ, Monotone (fun x => R x r m)) ∧
  (∀ x m : ℝ, MonotoneOn (fun r => R x r m) (Set.Icc (0 : ℝ) 1)) ∧
  (∀ x : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) 1, Monotone (fun m => R x r m)) ∧
  ∃ C : ℝ, ∀ x : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) 1, ∀ m : ℝ, |R x r m| ≤ C

/-- The class `ℛʳᵐ_b` (p. 7): bounded rewards `R(r, m)` independent of `x`, weakly increasing in
`r ∈ [0, 1]` and in `m`, and continuous in `m`. -/
def IsRMReward (R : ℝ → ℝ → ℝ) : Prop :=
  (∀ m : ℝ, MonotoneOn (fun r => R r m) (Set.Icc (0 : ℝ) 1)) ∧
  (∀ r ∈ Set.Icc (0 : ℝ) 1, Monotone (fun m => R r m)) ∧
  (∃ C : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) 1, ∀ m : ℝ, |R r m| ≤ C) ∧
  (∀ r ∈ Set.Icc (0 : ℝ) 1, Continuous (fun m => R r m))

/-- A reward `R(r, m)` of `ℛʳᵐ_b` viewed as a reward `R(x, r, m)` independent of `x`. -/
def lift (R : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun _ r m => R r m

/-- The mean `m_µ = ∫ y dµ(y)` of a measure on `ℝ`. -/
noncomputable def meanOf (μ : Measure ℝ) : ℝ := ∫ y, y ∂μ

/-- `R_µ(x) := R(x, F_µ(x), ∫ y dµ(y))` (p. 3), with `F_µ` the c.d.f. of `µ`. -/
noncomputable def Rmu (R : ℝ → ℝ → ℝ → ℝ) (μ : Measure ℝ) (x : ℝ) : ℝ :=
  R x (cdf μ x) (meanOf μ)

/-- The terminal project value `X_T = x0 + σ B_T` (p. 3, (2.3)). -/
def XT {Ω : Type*} (x0 σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ := x0 + σ * B T ω

/-- The admissible set `𝒬 = {Q ∈ 𝒫(Ω) : Q ∼ P}` (p. 4). -/
def Admissible {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : Prop :=
  IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q

/-- The objective of (2.3): `E^Q[R_µ̃(X_T)] − 2cσ² H(Q|P)`, used only where `H(Q|P) < ∞`. -/
noncomputable def objective {Ω : Type*} [MeasurableSpace Ω] (x0 σ c : ℝ) (T : ℝ≥0)
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (R : ℝ → ℝ → ℝ → ℝ) (μt : Measure ℝ) (Q : Measure Ω) : ℝ :=
  ∫ ω, Rmu R μt (XT x0 σ B T ω) ∂Q - 2 * c * σ ^ 2 * (InformationTheory.klDiv Q P).toReal

/-- The single player's value (2.3), p. 4:
`V(R, µ̃) := sup_{Q ∈ 𝒬} E^Q[R_µ̃(X_T)] − 2cσ² H(Q|P)`, the supremum taken over `Q ∼ P` with
`H(Q|P) < ∞` (the remaining `Q` have objective `−∞`). -/
noncomputable def V {Ω : Type*} [MeasurableSpace Ω] (x0 σ c : ℝ) (T : ℝ≥0)
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (R : ℝ → ℝ → ℝ → ℝ) (μt : Measure ℝ) : ℝ :=
  sSup {v : ℝ | ∃ Q : Measure Ω, Admissible P Q ∧ InformationTheory.klDiv Q P ≠ ⊤ ∧
    v = objective x0 σ c T P B R μt Q}

/-- `Q` is an optimal control for `V(R, µ̃)`: admissible, finite entropy, and attains the sup. -/
def IsOptimal {Ω : Type*} [MeasurableSpace Ω] (x0 σ c : ℝ) (T : ℝ≥0)
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (R : ℝ → ℝ → ℝ → ℝ) (μt : Measure ℝ) (Q : Measure Ω) :
    Prop :=
  Admissible P Q ∧ InformationTheory.klDiv Q P ≠ ⊤ ∧
    objective x0 σ c T P B R μt Q = V x0 σ c T P B R μt

/-- Equilibrium (p. 7): a probability law `µ` with a finite mean is a fixed point of the best
response `µ̃ ↦ Q_T`, where `Q` is an optimal control for `V(R, µ̃)`; `Q_T` is the law of `X_T`
under `Q`. The mean condition makes `R_µ` on p. 3 defined. -/
def IsEquilibrium {Ω : Type*} [MeasurableSpace Ω] (x0 σ c : ℝ) (T : ℝ≥0)
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (R : ℝ → ℝ → ℝ → ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ Integrable (fun y : ℝ => y) μ ∧
    ∃ Q : Measure Ω, IsOptimal x0 σ c T P B R μ Q ∧ Q.map (XT x0 σ B T) = μ

/-- The normal law `𝒩(x0, σ²T)`. -/
noncomputable def normalLaw (x0 σ : ℝ) (T : ℝ≥0) : Measure ℝ :=
  gaussianReal x0 (⟨σ ^ 2, sq_nonneg σ⟩ * T)

/-- (2.7), p. 5: `f0(x) := (1/(σ√T)) φ((x − x0)/(σ√T))`, `φ` the standard normal density. -/
noncomputable def f0 (x0 σ : ℝ) (T : ℝ≥0) (x : ℝ) : ℝ :=
  1 / (σ * Real.sqrt T) * gaussianPDFReal 0 1 ((x - x0) / (σ * Real.sqrt T))

/-- Proposition 2.1, p. 5: `β(µ̃) := ∫_ℝ f0(y) exp(R_µ̃(y)/(2cσ²)) dy`. -/
noncomputable def beta (x0 σ c : ℝ) (T : ℝ≥0) (R : ℝ → ℝ → ℝ → ℝ) (μt : Measure ℝ) : ℝ :=
  ∫ y, f0 x0 σ T y * Real.exp (Rmu R μt y / (2 * c * σ ^ 2))

/-- The (left-continuous) quantile function `q_µ(r) := inf {x | r ≤ F_µ(x)}`; used for
`r ∈ (0, 1)` only. -/
noncomputable def quantile (μ : Measure ℝ) (r : ℝ) : ℝ := sInf {x : ℝ | r ≤ cdf μ x}

/-- `N⁻¹`, the quantile function of the standard normal law. -/
noncomputable def Ninv (r : ℝ) : ℝ := quantile (gaussianReal 0 1) r

/-- The ratio inside `N⁻¹` in (3.2):
`∫_0^r exp(−R(z, m)/(2cσ²)) dz / ∫_0^1 exp(−R(z, m)/(2cσ²)) dz`. -/
noncomputable def ratio (σ c : ℝ) (R : ℝ → ℝ → ℝ) (m r : ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..r, Real.exp (-R z m / (2 * c * σ ^ 2))) /
    (∫ z in (0 : ℝ)..1, Real.exp (-R z m / (2 * c * σ ^ 2)))

/-- The right-hand side `g(m)` of (3.3): `x0 + σ√T ∫_0^1 N⁻¹(ratio(m, r)) dr`. -/
noncomputable def gmap (x0 σ c : ℝ) (T : ℝ≥0) (R : ℝ → ℝ → ℝ) (m : ℝ) : ℝ :=
  x0 + σ * Real.sqrt T * ∫ r in (0 : ℝ)..1, Ninv (ratio σ c R m r)

end TerminalRank.Equilibrium


