-- Prove2me | Definitions.Def_ConfoundRobust_Minimax_Setting
-- name    : ConfoundRobust_Minimax_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:20.877903+00:00
-- url     : https://prove2.me/theorems/edbe5e43-be60-4096-9e22-1ef64a4e3029
-- title:
--   §2, §4.1–4.2, §5, App. B.1, pp. 4–15, 38–41 — observations, policies, nominal propensity, 𝒲^Γ, 𝒲^Γ_n, Hájek regrets, worst-case regrets, W̄^Γ(π), VC-major dimension (Def. 1)
-- statement:
--   The objects of Kallus and Zhou's confounding-robust policy learning, all defined for observational data with $m$ discrete treatments.
--
--   1. **Observations.** A generic observation is a triple $(X, T, Y)$ of covariates $X \in \mathcal X$ (a measurable space), a treatment $T \in \{0, \dots, m-1\}$ and a real outcome $Y$, read as a loss (lower is better). The population is a probability measure $\mu$ on $\mathcal X \times \{0,\dots,m-1\} \times \mathbb R$, and a sample is a point $\omega = ((X_i,T_i,Y_i))_{i=1}^n$; the empirical expectation is $\mathbb E_n = \frac1n \sum_{i=1}^n$.
--   2. **Policies.** A policy $\pi$ assigns to each $x$ a probability vector $(\pi(t \mid x))_{t}$ on the treatments, measurably in $x$.
--   3. **Nominal propensity.** $\tilde e_t(x) = P(T = t \mid X = x)$, given as a measurable function satisfying $P(X \in A, T = t) = \mathbb E[\tilde e_t(X)\, \mathbb 1\{X \in A\}]$ for every measurable $A$.
--   4. **Weight box (marginal sensitivity model).** For $\Gamma \ge 1$,
--   $$a^\Gamma_t(x) = 1 + \Gamma^{-1}\Big(\frac{1}{\tilde e_t(x)} - 1\Big), \qquad b^\Gamma_t(x) = 1 + \Gamma\Big(\frac{1}{\tilde e_t(x)} - 1\Big).$$
--   The population uncertainty set $\mathcal W^\Gamma$ is the set of measurable weight functions $W(t,x,y)$ with $a^\Gamma_t(x) \le W(t,x,y) \le b^\Gamma_t(x)$ everywhere, and the sample set $\mathcal W^\Gamma_n$ (display (3)) is the set of vectors $w \in \mathbb R^n$ with $a^\Gamma_{T_i}(X_i) \le w_i \le b^\Gamma_{T_i}(X_i)$.
--   5. **Hájek regrets.** Relative to a baseline policy $\pi_0$, the population and sample regrets of $\pi$ under weights $W$ are $R_{\pi_0}(\pi; W) = \sum_{t=0}^{m-1} R^{(t)}_{\pi_0}(\pi;W)$ and $\hat R_{\pi_0}(\pi; W) = \sum_{t=0}^{m-1} \hat R^{(t)}_{\pi_0}(\pi;W)$, where
--   $$R^{(t)}_{\pi_0}(\pi; W) = \frac{\mathbb E[\mathbb I[T=t](\pi(t\mid X) - \pi_0(t\mid X)) W(T,X,Y) Y]}{\mathbb E[\mathbb I[T=t] W(T,X,Y)]}, \qquad \hat R^{(t)}_{\pi_0}(\pi; W) = \frac{\mathbb E_n[(\pi(t\mid X) - \pi_0(t\mid X))\mathbb I[T=t] Y W]}{\mathbb E_n[W\, \mathbb I[T=t]]}.$$
--   6. **Worst-case regrets.** $\bar R_{\pi_0}(\pi; \mathcal W) = \sup\{R_{\pi_0}(\pi; W) : W \in \mathcal W\}$ and, display (4), $\hat{\bar R}_{\pi_0}(\pi; \mathcal W_n) = \sup\{\hat R_{\pi_0}(\pi; w) : w \in \mathcal W_n\}$.
--   7. **Monotone weights (Proposition 3).** $\bar{\mathcal W}^\Gamma(\pi)$ is the set of $W(t,x,y) = a^\Gamma_t(x) + u\big(y(\pi(t\mid x) - \pi_0(t\mid x))\big)\,(b^\Gamma_t(x) - a^\Gamma_t(x))$ with $u : \mathbb R \to [0,1]$ nondecreasing, and $\bar{\mathcal W}^\Gamma_n(\pi)$ its restriction to the data. The quantity $y(\pi(t\mid x) - \pi_0(t\mid x))$ is called the score.
--   8. **VC-major dimension (Definition 1).** A class $F$ of real functions on a set $G$ has VC-major dimension at most $v$ if every finite set of points $\{g_1,\dots,g_k\}$ such that every subset is cut out by some superlevel set $\{f > \theta\}$, $f \in F$, $\theta \in \mathbb R$, has $k \le v$. The policy class $\Pi$ is viewed as the class of functions $(t,x) \mapsto \pi(t\mid x)$ (Assumption 3).
--   9. **Pointwise separability.** A class $F$ of real functions on $G$ is pointwise separable if some countable $F_0 \subseteq F$ approximates every $f \in F$ pointwise: there are $f_k \in F_0$ with $f_k(g) \to f(g)$ for every $g \in G$ (van der Vaart and Wellner 1996, Example 2.3.4). This is the measurability condition of empirical process theory; it is not printed in the paper.
--   10. **Auxiliary objects.** Lemma 2's function $f(\pi)(x,t,y) = (\pi(t\mid x) - 1/m)\, y$; Lemma 4's composition class $\bar{\mathcal U}^\Gamma = \{(x,t,y) \mapsto u(y(\pi(t\mid x) - \pi_0(t\mid x))) : \pi \in \Pi,\ u \text{ nondecreasing } \mathbb R \to [0,1]\}$; and the rates $c\,(12+\nu^{-1})(BK + \nu^{-1}(\Gamma-\Gamma^{-1})(K+B+m))\sqrt{\log(15m/\delta)/n}$ with $c = 36$ (Corollary 7) and $c = 18$ (end of the proof of Theorem 6).
--
--   These definitions are shared by every statement of the mission: the goal compares the worst-case population regret of the sample-optimal policy with the population minimax regret, both suprema of Hájek regrets over the weight box.
--
--   **Formalization Note** Treatments are `Fin m` (0-indexed, as on the page); `π x t` is $\pi(t\mid x)$. Weight functions in $\mathcal W^\Gamma$ are required to be measurable, and policies to be measurable in $x$: the paper does not say so, but without it the Bochner integral of a non-integrable function is $0$ and the supremum would range over junk values. $\mathbb E_n$ is $(1/n)\sum_i$; a treatment group with no sample gives the Hájek ratio $0/0 = 0$ in Lean (the paper ignores this case, whose probability is at most $m(1-\nu)^n$ under overlap). Suprema and infima are real `sSup`/`sInf`; under the standing hypotheses of the theorems ($\nu \le \tilde e \le 1$, bounded outcomes) the weight sets are nonempty (they contain $1/\tilde e$) and the regrets are bounded, so these are true suprema. VC-major dimension is encoded as the predicate "at most $v$", not as a supremum of naturals.
-- source:
--   Kallus & Zhou, arXiv:1805.08593v3, §2 (pp. 4–5), §4.1 displays (2)–(4) (pp. 9–10), §4.2 (p. 10), Definition 1 and Assumption 3 (p. 13), Proposition 3 (pp. 14–15), Appendix B.1 (pp. 38–41)

import Mathlib

open MeasureTheory

namespace ConfoundRobust.Minimax

/-- An observation `(X, T, Y)`: covariates `X ∈ 𝒳`, a treatment `T ∈ {0, …, m − 1}` and a real
outcome (loss) `Y`. Write `z.1` for `X`, `z.2.1` for `T` and `z.2.2` for `Y`. -/
abbrev Obs (𝒳 : Type) (m : ℕ) : Type := 𝒳 × Fin m × ℝ

variable {𝒳 : Type} [MeasurableSpace 𝒳] {m : ℕ}

/-- `π x t` is the probability `π(t | x)` that the policy assigns treatment `t` at covariates `x`:
a measurable map `𝒳 → Δ^m` into the probability simplex. -/
def IsPolicy (π : 𝒳 → Fin m → ℝ) : Prop :=
  (∀ t, Measurable (fun x => π x t)) ∧ ∀ x, (∀ t, 0 ≤ π x t) ∧ ∑ t, π x t = 1

/-- `e t` is a measurable version of the nominal propensity `ẽ_t(x) = P(T = t | X = x)` under the
law `μ` of `(X, T, Y)`: `P(X ∈ A, T = t) = E[ẽ_t(X); X ∈ A]` for every measurable `A`. -/
def IsNominalPropensity (μ : Measure (Obs 𝒳 m)) (e : Fin m → 𝒳 → ℝ) : Prop :=
  (∀ t, Measurable (e t)) ∧
    ∀ (t : Fin m) (A : Set 𝒳), MeasurableSet A →
      μ.real {z : Obs 𝒳 m | z.1 ∈ A ∧ z.2.1 = t} = ∫ z in {z : Obs 𝒳 m | z.1 ∈ A}, e t z.1 ∂μ

/-- `a^Γ_t(x) = 1 + Γ⁻¹ (1 / ẽ_t(x) − 1)`, the lower end of the weight box. -/
noncomputable def aG (Γ : ℝ) (e : Fin m → 𝒳 → ℝ) (t : Fin m) (x : 𝒳) : ℝ :=
  1 + Γ⁻¹ * (1 / e t x - 1)

/-- `b^Γ_t(x) = 1 + Γ (1 / ẽ_t(x) − 1)`, the upper end of the weight box. -/
noncomputable def bG (Γ : ℝ) (e : Fin m → 𝒳 → ℝ) (t : Fin m) (x : 𝒳) : ℝ :=
  1 + Γ * (1 / e t x - 1)

/-- The population uncertainty set `𝒲^Γ` (§4.2): measurable weight functions `W(t, x, y)` with
`a^Γ_t(x) ≤ W(t, x, y) ≤ b^Γ_t(x)` everywhere. -/
def WSet (Γ : ℝ) (e : Fin m → 𝒳 → ℝ) : Set (Obs 𝒳 m → ℝ) :=
  {W | Measurable W ∧ ∀ z : Obs 𝒳 m, aG Γ e z.2.1 z.1 ≤ W z ∧ W z ≤ bG Γ e z.2.1 z.1}

/-- The sample uncertainty set `𝒲^Γ_n` (3): weight vectors `w ∈ ℝ^n` with
`a^Γ_{T_i}(X_i) ≤ w_i ≤ b^Γ_{T_i}(X_i)`. -/
def WSetN {n : ℕ} (Γ : ℝ) (e : Fin m → 𝒳 → ℝ) (ω : Fin n → Obs 𝒳 m) : Set (Fin n → ℝ) :=
  {w | ∀ i, aG Γ e (ω i).2.1 (ω i).1 ≤ w i ∧ w i ≤ bG Γ e (ω i).2.1 (ω i).1}

/-- The population Hájek regret of treatment level `t` (§4.2):
`R^(t)_{π₀}(π; W) = E[I[T = t](π(t|X) − π₀(t|X)) W(T,X,Y) Y] / E[I[T = t] W(T,X,Y)]`. -/
noncomputable def regretT (μ : Measure (Obs 𝒳 m)) (π π0 : 𝒳 → Fin m → ℝ) (W : Obs 𝒳 m → ℝ)
    (t : Fin m) : ℝ :=
  (∫ z, (if z.2.1 = t then (π z.1 t - π0 z.1 t) * W z * z.2.2 else 0) ∂μ) /
    (∫ z, (if z.2.1 = t then W z else 0) ∂μ)

/-- The population regret `R_{π₀}(π; W) = Σ_t R^(t)_{π₀}(π; W)`. -/
noncomputable def regret (μ : Measure (Obs 𝒳 m)) (π π0 : 𝒳 → Fin m → ℝ) (W : Obs 𝒳 m → ℝ) : ℝ :=
  ∑ t, regretT μ π π0 W t

/-- The worst-case population regret `R̄_{π₀}(π; 𝒲) = sup {R_{π₀}(π; W) : W ∈ 𝒲}`. -/
noncomputable def worstRegret (μ : Measure (Obs 𝒳 m)) (π π0 : 𝒳 → Fin m → ℝ)
    (𝒲 : Set (Obs 𝒳 m → ℝ)) : ℝ :=
  sSup ((fun W => regret μ π π0 W) '' 𝒲)

/-- The sample Hájek regret of treatment level `t` (§4.1):
`R̂^(t)_{π₀}(π; W) = E_n[(π(t|X) − π₀(t|X)) I[T = t] Y W] / E_n[W I[T = t]]`, with `E_n = (1/n) Σ_i`.
An empty treatment group gives `0 / 0 = 0`. -/
noncomputable def sRegretT {n : ℕ} (ω : Fin n → Obs 𝒳 m) (π π0 : 𝒳 → Fin m → ℝ) (w : Fin n → ℝ)
    (t : Fin m) : ℝ :=
  ((n : ℝ)⁻¹ * ∑ i, if (ω i).2.1 = t then (π (ω i).1 t - π0 (ω i).1 t) * (ω i).2.2 * w i else 0) /
    ((n : ℝ)⁻¹ * ∑ i, if (ω i).2.1 = t then w i else 0)

/-- The sample regret `R̂_{π₀}(π; W) = Σ_t R̂^(t)_{π₀}(π; W)`. -/
noncomputable def sRegret {n : ℕ} (ω : Fin n → Obs 𝒳 m) (π π0 : 𝒳 → Fin m → ℝ) (w : Fin n → ℝ) : ℝ :=
  ∑ t, sRegretT ω π π0 w t

/-- The worst-case sample regret (4): `sup {R̂_{π₀}(π; W) : W ∈ 𝒲_n}`. -/
noncomputable def sWorstRegret {n : ℕ} (ω : Fin n → Obs 𝒳 m) (π π0 : 𝒳 → Fin m → ℝ)
    (𝒲n : Set (Fin n → ℝ)) : ℝ :=
  sSup ((fun w => sRegret ω π π0 w) '' 𝒲n)

/-- The score `y (π(t | x) − π₀(t | x))` of an observation `(x, t, y)`. -/
def score (π π0 : 𝒳 → Fin m → ℝ) (z : Obs 𝒳 m) : ℝ :=
  z.2.2 * (π z.1 z.2.1 - π0 z.1 z.2.1)

/-- `u : ℝ → [0, 1]` is monotonic nondecreasing. -/
def IsUnitMonotone (u : ℝ → ℝ) : Prop :=
  Monotone u ∧ ∀ s, 0 ≤ u s ∧ u s ≤ 1

/-- The monotone weight class `𝒲̄^Γ(π)` of Proposition 3:
`W(t, x, y) = a^Γ_t(x) + u(y(π(t|x) − π₀(t|x))) (b^Γ_t(x) − a^Γ_t(x))`, `u : ℝ → [0,1]` nondecreasing. -/
def WbarSet (Γ : ℝ) (e : Fin m → 𝒳 → ℝ) (π π0 : 𝒳 → Fin m → ℝ) : Set (Obs 𝒳 m → ℝ) :=
  {W | ∃ u, IsUnitMonotone u ∧
    ∀ z : Obs 𝒳 m, W z = aG Γ e z.2.1 z.1 + u (score π π0 z) * (bG Γ e z.2.1 z.1 - aG Γ e z.2.1 z.1)}

/-- `𝒲̄^Γ_n(π) = {(W(T₁,X₁,Y₁), …, W(Tₙ,Xₙ,Yₙ)) : W ∈ 𝒲̄^Γ(π)}`, the restriction to the data. -/
def WbarSetN {n : ℕ} (Γ : ℝ) (e : Fin m → 𝒳 → ℝ) (π π0 : 𝒳 → Fin m → ℝ) (ω : Fin n → Obs 𝒳 m) :
    Set (Fin n → ℝ) :=
  (fun W => fun i => W (ω i)) '' WbarSet Γ e π π0

/-- Definition 1, as an upper bound: the VC-major dimension of `F ⊆ [G → ℝ]` is at most `v`, i.e.
every finite set of points on which the superlevel sets `{f > θ}` (`f ∈ F`, `θ ∈ ℝ`) cut out every
subset has at most `v` points. -/
def VCMajorLE {G : Type*} (F : Set (G → ℝ)) (v : ℕ) : Prop :=
  ∀ s : Finset G, (∀ A ⊆ s, ∃ f ∈ F, ∃ θ : ℝ, ∀ g ∈ s, (g ∈ A ↔ θ < f g)) → s.card ≤ v

/-- The class `F ⊆ [G → ℝ]` is pointwise separable (pointwise measurable): some countable subclass
`F₀ ⊆ F` approximates every `f ∈ F` pointwise, `f_k(g) → f(g)` for every `g ∈ G` (van der Vaart and
Wellner 1996, Example 2.3.4). This is the measurability condition under which the symmetrization and
chaining bounds of empirical process theory hold. -/
def PointwiseSeparable {G : Type*} (F : Set (G → ℝ)) : Prop :=
  ∃ F₀ ⊆ F, F₀.Countable ∧ ∀ f ∈ F, ∃ s : ℕ → G → ℝ, (∀ k, s k ∈ F₀) ∧
    ∀ g, Filter.Tendsto (fun k => s k g) Filter.atTop (nhds (f g))

/-- The policy class as a class of functions `(t, x) ↦ π(t | x)` on `{0, …, m − 1} × 𝒳`
(Assumption 3). -/
def policyFns (P : Set (𝒳 → Fin m → ℝ)) : Set (Fin m × 𝒳 → ℝ) :=
  (fun π => fun g => π g.2 g.1) '' P

/-- Lemma 2's `f(π)(x, t, y) = (π(t | x) − 1/m) y`. -/
noncomputable def fPol (π : 𝒳 → Fin m → ℝ) (z : Obs 𝒳 m) : ℝ :=
  (π z.1 z.2.1 - 1 / (m : ℝ)) * z.2.2

/-- Lemma 4's composition class `𝒰̄^Γ`: the functions `(x, t, y) ↦ u(y(π(t|x) − π₀(t|x)))` with
`π ∈ Π` and `u : ℝ → [0, 1]` nondecreasing. -/
def compClass (P : Set (𝒳 → Fin m → ℝ)) (π0 : 𝒳 → Fin m → ℝ) : Set (Obs 𝒳 m → ℝ) :=
  {W | ∃ π ∈ P, ∃ u, IsUnitMonotone u ∧ W = fun z => u (score π π0 z)}

/-- The rate of Corollary 7:
`36 (12 + ν⁻¹)(B K + ν⁻¹ (Γ − Γ⁻¹)(K + B + m)) √(log(15 m / δ) / n)`. -/
noncomputable def rateCor7 (ν B Γ K : ℝ) (m n : ℕ) (δ : ℝ) : ℝ :=
  36 * (12 + ν⁻¹) * (B * K + ν⁻¹ * (Γ - Γ⁻¹) * (K + B + m)) * Real.sqrt (Real.log (15 * m / δ) / n)

/-- The rate at the end of the proof of Theorem 6:
`18 (12 + ν⁻¹)(B K + ν⁻¹ (Γ − Γ⁻¹)(K + B + m)) √(log(15 m / δ) / n)`. -/
noncomputable def rateThm6 (ν B Γ K : ℝ) (m n : ℕ) (δ : ℝ) : ℝ :=
  18 * (12 + ν⁻¹) * (B * K + ν⁻¹ * (Γ - Γ⁻¹) * (K + B + m)) * Real.sqrt (Real.log (15 * m / δ) / n)

end ConfoundRobust.Minimax


