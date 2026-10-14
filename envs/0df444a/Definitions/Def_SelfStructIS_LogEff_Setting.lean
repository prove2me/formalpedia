-- Prove2me | Definitions.Def_SelfStructIS_LogEff_Setting
-- name    : SelfStructIS_LogEff_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:28:33.330024+00:00
-- url     : https://prove2.me/theorems/378f1536-d94b-4f35-ba0c-52fa5d6d4e16
-- title:
--   §2–§5.2, pp. 5–16 — hazards, left-continuous inverses, t(u), Assumptions 2.1, 3.1, 3.2, 5.1
-- statement:
--   This file fixes the probabilistic model of Deo and Murthy's self-structuring importance sampler.
--
--   Let $X=(X_1,\dots,X_d)$ be a random vector in $\mathbb R^d$ with law $\mu$, and write $\mathbb R^d_+=\{x: x\ge 0\}$, $\mathbb R^d_{++}=\{x : x>0\}$ (componentwise), and $\|x\|=\max_i |x_i|$.
--
--   1. **Marginal hazards** (§3.2, p. 10). The survival function and cumulative hazard of $X_i$ are
--   $$\bar F_i(x)=P(X_i>x),\qquad \Lambda_i(x)=-\log \bar F_i(x),$$
--   and $\Lambda(x)=(\Lambda_1(x_1),\dots,\Lambda_d(x_d))$; the standardized vector is $Y=\Lambda(X)$.
--   2. **Left-continuous inverses** ((14), p. 12). $q_i(y)=\Lambda_i^{\leftarrow}(y)=\inf\{x:\Lambda_i(x)\ge y\}$, $q(y)=(q_1(y_1),\dots,q_d(y_d))$, $q_\infty(t)=\|q(t\mathbf 1)\|$, $\hat q(t)=q(t\mathbf 1)/q_\infty(t)$, $\Lambda_{\min}(u)=\min_i\Lambda_i(u)$, and, for the growth index $\rho$ of the loss, $t(u)=\Lambda_{\min}(u^{1/\rho})$ ((34b), p. 27). The limit $q^*=\lim_{t\to\infty}\hat q(t)$, when it exists, is stated as a hypothesis wherever it is used.
--   3. **Slow variation** ((11), p. 9). A function $f$ is slowly varying if it is eventually positive and $f(sx)/f(s)\to 1$ as $s\to\infty$ for every $x>0$ (regular variation with index $0$).
--   4. **Assumption 2.1** (pp. 5–6). The loss $L:\mathbb R^d\to\mathbb R$ satisfies: $\rho>0$; (a) $\{x\in\operatorname{supp}(X): L(x)\ge u\}\subseteq\mathbb R^d_+$ for all sufficiently large $u$; (b) for every sequence $x_n\to x$ in $\mathbb R^d_+$,
--   $$\lim_{n\to\infty}\frac{L(nx_n)}{n^\rho}=L^*(x);$$
--   and the cone $\{x\in\mathbb R^d_+: L^*(x)>0\}$ is non-empty.
--   5. **Assumption 3.1** (p. 10). For every $i$: $\alpha_i\in(0,\infty)$, $\Lambda_i$ is continuous, strictly increasing on some interval $(x_0,\infty)$, and regularly varying with index $\alpha_i$.
--   6. **Assumption 3.2** (p. 10). $Y=\Lambda(X)$ has density $f_Y(y)=p(y)e^{-\varphi(y)}$ (12), and there is $I:\mathbb R^d_+\to\mathbb R_+$ such that, for every sequence $y_n\to y\neq 0$ in $\mathbb R^d_+$ and every $\varepsilon>0$,
--   $$n^{-1}\varphi(ny_n)\to I(y),\qquad n^{-\varepsilon}\log p(ny_n)\to 0 \quad (13).$$
--   7. **Assumption 5.1** (p. 16). There is $x_0>0$ such that each $\Lambda_i$ is convex or concave on $[x_0,\infty)$.
--
--   These are the standing assumptions of the paper's tail-modelling framework; every statement of the mission draws its hypotheses from this list.
--
--   **Formalization Note** Points of $\mathbb R^d$ are `Fin d → ℝ` (components are 0-based) with the sup norm, which is the paper's $\ell_\infty$-norm. Regular variation is the published `HeavyTailNV.Tail.IsRegularlyVarying` (real-variable limit with an eventually positive denominator, the standard de Haan–Ferreira form of (11)). $\operatorname{supp}(X)$ is Mathlib's `Measure.support`. In (13) the requirement "$p(ny_n)>0$ for all large $n$" is written out, since the logarithm in (13) presupposes it; without it a density vanishing on a tail region would pass through Lean's convention $\log 0=0$. The law of $Y$ is the push-forward of $\mu$ under $\Lambda$, which is measurable because each $\Lambda_i$ is monotone. $I$ and $L^*$ are stored on all of $\mathbb R^d$ but only their values on $\mathbb R^d_+$ are constrained. Where $\bar F_i=0$ Lean's $\Lambda_i$ is $0$ rather than $+\infty$; continuity and eventual strict monotonicity in Assumption 3.1 exclude that.
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, pp. 5–6, Assumption 2.1; p. 9, (11); p. 10, Assumptions 3.1, 3.2, (12), (13); p. 12, (14); p. 16, Assumption 5.1; p. 27, (34b)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

namespace SelfStructIS.LogEff

open MeasureTheory Filter Topology

/-- Slow variation, §3.1, p. 9: regular variation with index `0`
(`HeavyTailNV.Tail.IsRegularlyVarying`, the real-variable form of (11) with an eventually
positive denominator). -/
def SlowlyVarying (f : ℝ → ℝ) : Prop :=
  HeavyTailNV.Tail.IsRegularlyVarying f 0

variable {d : ℕ}

/-- The marginal survival function `F̄ᵢ(x) = P(Xᵢ > x)` of the law `μ` of `X`, §3.2, p. 10.
Components are 0-based. -/
noncomputable def survival (μ : Measure (Fin d → ℝ)) (i : Fin d) (x : ℝ) : ℝ :=
  (μ {y | x < y i}).toReal

/-- The marginal cumulative hazard `Λᵢ(x) = -log F̄ᵢ(x)`, §3.2, p. 10. -/
noncomputable def hazard (μ : Measure (Fin d → ℝ)) (i : Fin d) (x : ℝ) : ℝ :=
  -Real.log (survival μ i x)

/-- The standardizing map `Λ(x) = (Λ₁(x₁), …, Λ_d(x_d))`, §3.2, p. 10. -/
noncomputable def hazardVec (μ : Measure (Fin d → ℝ)) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => hazard μ i (x i)

/-- `Λ_min(u) = minᵢ Λᵢ(u)`, (14), p. 12. -/
noncomputable def hazardMin (μ : Measure (Fin d → ℝ)) (u : ℝ) : ℝ :=
  ⨅ i : Fin d, hazard μ i u

/-- The left-continuous inverse `qᵢ(y) = Λᵢ^←(y) = inf {x : Λᵢ(x) ≥ y}`, (14), p. 12
(used only at `y > 0`). -/
noncomputable def qinv (μ : Measure (Fin d → ℝ)) (i : Fin d) (y : ℝ) : ℝ :=
  sInf {x : ℝ | y ≤ hazard μ i x}

/-- The componentwise inverse `q(y) = (q₁(y₁), …, q_d(y_d))`, (14), p. 12. -/
noncomputable def qvec (μ : Measure (Fin d → ℝ)) (y : Fin d → ℝ) : Fin d → ℝ :=
  fun i => qinv μ i (y i)

/-- `q_∞(t) = ‖q(t𝟏)‖_∞`, (34b), p. 27 (the norm on `Fin d → ℝ` is the sup norm). -/
noncomputable def qinfty (μ : Measure (Fin d → ℝ)) (t : ℝ) : ℝ :=
  ‖qvec μ (fun _ => t)‖

/-- `q̂(t) = q(t𝟏)/‖q(t𝟏)‖_∞`, (14), p. 12. -/
noncomputable def qhat (μ : Measure (Fin d → ℝ)) (t : ℝ) : Fin d → ℝ :=
  (qinfty μ t)⁻¹ • qvec μ (fun _ => t)

/-- `t(u) = Λ_min(u^{1/ρ})`, (34b), p. 27. -/
noncomputable def tfun (μ : Measure (Fin d → ℝ)) (ρ u : ℝ) : ℝ :=
  hazardMin μ (u ^ (1 / ρ))

/-- Assumption 2.1, pp. 5–6, on the loss `L` with growth index `ρ` and limit `L*`:
`ρ > 0`; (a) for all sufficiently large `u`, `{x ∈ supp(X) : L(x) ≥ u} ⊆ ℝᵈ₊`;
(b) `L(n xₙ)/n^ρ → L*(x)` for every sequence `xₙ → x` in `ℝᵈ₊`; and `{x ∈ ℝᵈ₊ : L*(x) > 0} ≠ ∅`.
`L*` is stored on `Fin d → ℝ` and only its values on `ℝᵈ₊` are constrained. -/
def Assumption21 (μ : Measure (Fin d → ℝ)) (L : (Fin d → ℝ) → ℝ) (ρ : ℝ)
    (Lstar : (Fin d → ℝ) → ℝ) : Prop :=
  0 < ρ ∧
  (∀ᶠ u in atTop, ∀ x ∈ μ.support, u ≤ L x → ∀ i, 0 ≤ x i) ∧
  (∀ (xs : ℕ → Fin d → ℝ) (x : Fin d → ℝ), (∀ n i, 0 ≤ xs n i) →
    Tendsto xs atTop (𝓝 x) →
    Tendsto (fun n : ℕ => L ((n : ℝ) • xs n) / (n : ℝ) ^ ρ) atTop (𝓝 (Lstar x))) ∧
  (∃ x : Fin d → ℝ, (∀ i, 0 ≤ x i) ∧ 0 < Lstar x)

/-- Assumption 3.1, p. 10, with tail indices `α`: for every `i`, `αᵢ ∈ (0, ∞)`, `Λᵢ` is
continuous, strictly increasing on some interval `(x₀, ∞)`, and `Λᵢ ∈ 𝓡𝓥(αᵢ)`. -/
def Assumption31 (μ : Measure (Fin d → ℝ)) (α : Fin d → ℝ) : Prop :=
  ∀ i, 0 < α i ∧ Continuous (hazard μ i) ∧
    (∃ x₀ : ℝ, StrictMonoOn (hazard μ i) (Set.Ioi x₀)) ∧
    HeavyTailNV.Tail.IsRegularlyVarying (hazard μ i) (α i)

/-- The convergences (13), p. 10: for every sequence `yₙ → y ≠ 0` in `ℝᵈ₊`,
`n⁻¹ φ(n yₙ) → I(y)`, `p(n yₙ) > 0` for all large `n`, and `n^{-ε} log p(n yₙ) → 0` for every
`ε > 0`. -/
def Conv13 (p φ I : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (ys : ℕ → Fin d → ℝ) (y : Fin d → ℝ), (∀ n i, 0 ≤ ys n i) →
    Tendsto ys atTop (𝓝 y) → y ≠ 0 →
    Tendsto (fun n : ℕ => φ ((n : ℝ) • ys n) / (n : ℝ)) atTop (𝓝 (I y)) ∧
    (∀ᶠ n : ℕ in atTop, 0 < p ((n : ℝ) • ys n)) ∧
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => Real.log (p ((n : ℝ) • ys n)) / (n : ℝ) ^ ε) atTop (𝓝 0)

/-- Assumption 3.2, p. 10: `Y = Λ(X)` has density `f_Y(y) = p(y) exp(-φ(y))` (12), with a
limiting function `I : ℝᵈ₊ → ℝ₊` such that (13) holds. `I` is stored on `Fin d → ℝ`; only its
values on `ℝᵈ₊` are constrained. -/
def Assumption32 (μ : Measure (Fin d → ℝ)) (p φ I : (Fin d → ℝ) → ℝ) : Prop :=
  μ.map (hazardVec μ) =
      volume.withDensity (fun y => ENNReal.ofReal (p y * Real.exp (-φ y))) ∧
    (∀ y : Fin d → ℝ, (∀ i, 0 ≤ y i) → 0 ≤ I y) ∧
    Conv13 p φ I

/-- Assumption 5.1, p. 16: there is `x₀ > 0` such that every `Λᵢ` is convex or concave on
`[x₀, ∞)`. -/
def Assumption51 (μ : Measure (Fin d → ℝ)) : Prop :=
  ∃ x₀ : ℝ, 0 < x₀ ∧
    ∀ i, ConvexOn ℝ (Set.Ici x₀) (hazard μ i) ∨ ConcaveOn ℝ (Set.Ici x₀) (hazard μ i)

end SelfStructIS.LogEff


