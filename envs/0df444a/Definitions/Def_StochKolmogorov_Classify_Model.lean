-- Prove2me | Definitions.Def_StochKolmogorov_Classify_Model
-- name    : StochKolmogorov_Classify_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:30:11.919215+00:00
-- url     : https://prove2.me/theorems/a2f398bf-43bd-49b1-a687-e1e66bcb01eb
-- title:
--   §1.1 and §3, pp. 3–5, 13–14 — the Kolmogorov SDE (1.1), invariant and ergodic measures, M, Conv, λᵢ, Assumption 1.1, the constants of (3.1)–(3.5)
-- statement:
--   This module sets up the stochastic Kolmogorov system of Hening and Nguyen and the objects every statement of the paper is about.
--
--   Let $n \ge 1$. The state space is the closed orthant $\mathbb R^n_+ = [0,\infty)^n$, with interior $\mathbb R^{n,\circ}_+ = (0,\infty)^n$ and boundary $\partial\mathbb R^n_+ = \mathbb R^n_+ \setminus \mathbb R^{n,\circ}_+$; the norm is $\|x\| = \sum_i |x_i|$. Given per-capita growth rates $f_i$, noise intensities $g_i$ and a matrix $\Gamma$, the process solves
--
--   $$
--   dX_i(t) = X_i(t) f_i(X(t))\,dt + X_i(t) g_i(X(t))\,dE_i(t),\qquad i = 1,\dots,n,
--   $$
--
--   where $E(t) = \Gamma^\top B(t)$ for an $n$-dimensional standard Brownian motion $B$, so that $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$ is the covariance of $E$.
--
--   The module defines:
--   1. the drift $x_i f_i(x)$ and the diffusion matrix with entries $x_i g_i(x) \Gamma_{ji}$ (because $dE_i = \sum_j \Gamma_{ji}\, dB_j$);
--   2. a *solution family*: one probability space, one Brownian motion $B$, and for every $x \in \mathbb R^n_+$ a strong solution $X^x$ of (1.1) started at $x$;
--   3. the transition probability $P_X(t,x,\cdot)$, the mean occupation measure $\Pi^x_t = \frac1t\int_0^t P_X(s,x,\cdot)\,ds$, invariant probability measures (supported on $\mathbb R^n_+$), and ergodic ones (extreme points of the invariant probability measures);
--   4. $\mathcal M$, the ergodic invariant probability measures supported on $\partial\mathbb R^n_+$, and $\mathrm{Conv}(\widetilde{\mathcal M})$, the finite convex combinations with positive weights of elements of $\widetilde{\mathcal M}$;
--   5. the Lyapunov exponents $\lambda_i(\mu) = \int (f_i(x) - \sigma_{ii} g_i^2(x)/2)\,\mu(dx)$;
--   6. Assumption 1.1: $(g_i(x)g_j(x)\sigma_{ij})$ positive definite on $\mathbb R^n_+$, $f_i, g_i$ locally Lipschitz on $\mathbb R^n_+$, and the dissipativity condition (1.2)
--   $$
--   \limsup_{\|x\|\to\infty}\Big[\frac{\sum_i c_i x_i f_i(x)}{1+c^\top x} - \frac12\frac{\sum_{i,j}\sigma_{ij}c_ic_jx_ix_jg_i(x)g_j(x)}{(1+c^\top x)^2} + \gamma_b\Big(1+\sum_i(|f_i(x)|+g_i^2(x))\Big)\Big] < 0
--   $$
--   for some $c \in \mathbb R^{n,\circ}_+$, $\gamma_b > 0$;
--   7. the constants of §3: the radius $M$ of (3.1), $\delta_0 \in (0,\gamma_b/2)$ with (3.2), the supremum $H$ of (3.5) and the function $V(x) = (1+c^\top x)/\prod_i x_i^{p_i}$ of (3.4).
--
--   These objects are shared by the three missions on this paper.
--
--   **Formalization Note** The coefficients $f_i, g_i$ are functions on all of $\mathbb R^n$, constrained only on $\mathbb R^n_+$; the drift and diffusion read them at the componentwise positive part $x^+$, which equals $x$ on $\mathbb R^n_+$, the only region a solution started in $\mathbb R^n_+$ visits (Lemma 3.1). The $\limsup < 0$ of (1.2) is written in the equivalent form "the bracket is $\le -\varepsilon$ whenever $\|x\| \ge R$". "Ergodic" is not defined in the paper and is encoded as extremality among invariant probability measures. Coordinates are indexed by `Fin n`, 0-based.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, §1.1, pp. 3–5, and §3, pp. 13–14, (1.1), (1.2), Assumption 1.1, (3.1)–(3.5)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SolvesBrownianSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify

open EthierKurtz

/-- `ℝⁿ₊ = [0, ∞)ⁿ` (arXiv:1704.06984v1, §1.1, p. 3). -/
def orthant (n : ℕ) : Set (SDEState n) := {x | ∀ i, 0 ≤ x i}

/-- `ℝⁿ,◦₊ = (0, ∞)ⁿ` (p. 3). -/
def openOrthant (n : ℕ) : Set (SDEState n) := {x | ∀ i, 0 < x i}

/-- `∂ℝⁿ₊ = ℝⁿ₊ \ ℝⁿ,◦₊` (p. 5). -/
def bdry (n : ℕ) : Set (SDEState n) := orthant n \ openOrthant n

/-- The norm `‖x‖ = ∑ᵢ |xᵢ|` of p. 4 (not the Euclidean norm of `SDEState n`). -/
def l1 {n : ℕ} (x : SDEState n) : ℝ := ∑ i, |x i|

/-- The coefficients of (1.1) (p. 3): per-capita growth rates `f i`, noise intensities `g i`,
and the matrix `Γ` with `E(t) = Γᵀ B(t)`. -/
structure Coeffs (n : ℕ) where
  f : Fin n → SDEState n → ℝ
  g : Fin n → SDEState n → ℝ
  Γ : Matrix (Fin n) (Fin n) ℝ

/-- `σᵢⱼ`, the entries of `Σ = ΓᵀΓ` (p. 3). -/
def Coeffs.sig {n : ℕ} (C : Coeffs n) (i j : Fin n) : ℝ := (C.Γ.transpose * C.Γ) i j

/-- Componentwise positive part `x⁺`. The coefficients of (1.1) are read at `x⁺`, which is `x`
on `ℝⁿ₊`, the only region a solution started in `ℝⁿ₊` visits (Lemma 3.1). -/
noncomputable def posPart {n : ℕ} (x : SDEState n) : SDEState n :=
  WithLp.toLp 2 (fun i => max (x i) 0)

/-- Drift of (1.1): `xᵢ fᵢ(x)`, time-homogeneous. -/
noncomputable def drift {n : ℕ} (C : Coeffs n) : ℝ≥0 × SDEState n → SDEState n :=
  fun p => WithLp.toLp 2 (fun i => p.2 i * C.f i (posPart p.2))

/-- Diffusion of (1.1): entry `(i, j)` is `xᵢ gᵢ(x) Γⱼᵢ`, because `dEᵢ = ∑ⱼ Γⱼᵢ dBⱼ`. -/
noncomputable def diffusion {n : ℕ} (C : Coeffs n) : ℝ≥0 × SDEState n → SDEDiffusion n :=
  fun p => WithLp.toLp 2 (fun ij : Fin n × Fin n =>
    p.2 ij.1 * C.g ij.1 (posPart p.2) * C.Γ ij.2 ij.1)

/-- A family of strong solutions of (1.1), one from each `x ∈ ℝⁿ₊`, all driven by one standard
Brownian motion `B` on one probability space: `X x` is the paper's process under `ℙₓ`. -/
def IsSolutionFamily {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Prop :=
  IsProbabilityMeasure P ∧ IsStandardBrownian P B ∧
    ∀ x ∈ orthant n, SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) (X x)

/-- The transition probability `P_X(t, x, ·)` (p. 4): the law of `X(t)` under `ℙₓ`. -/
noncomputable def trans {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (t : ℝ≥0) (x : SDEState n) :
    Measure (SDEState n) :=
  P.map (X x t)

/-- The mean occupation measure `Πˣₜ(·) = (1/t) ∫₀ᵗ ℙₓ{X(s) ∈ ·} ds` (p. 14). -/
noncomputable def occMean {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (t : ℝ) :
    Measure (SDEState n) :=
  (ENNReal.ofReal t)⁻¹ •
    ((volume.restrict (Set.Icc (0 : ℝ) t)).prod P).map (fun q => X x q.1.toNNReal q.2)

/-- `μ` is an invariant probability measure of `X` on `ℝⁿ₊`. -/
def IsInvariant {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (μ : Measure (SDEState n)) : Prop :=
  IsProbabilityMeasure μ ∧ μ (orthant n)ᶜ = 0 ∧
    ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      ∫⁻ x, trans P X t x A ∂μ = μ A

/-- `μ` is an ergodic invariant probability measure: an extreme point of the convex set of
invariant probability measures. -/
def IsErgodic {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (μ : Measure (SDEState n)) : Prop :=
  IsInvariant P X μ ∧
    ∀ ν₁ ν₂ : Measure (SDEState n), IsInvariant P X ν₁ → IsInvariant P X ν₂ →
      ∀ a : ℝ≥0, 0 < a → a < 1 →
        μ = (a : ℝ≥0∞) • ν₁ + ((1 - a : ℝ≥0) : ℝ≥0∞) • ν₂ → ν₁ = μ

/-- `M`, the ergodic invariant probability measures of `X` supported on `∂ℝⁿ₊` (p. 5). -/
def bdryErgodic {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Set (Measure (SDEState n)) :=
  {μ | IsErgodic P X μ ∧ μ (openOrthant n) = 0}

/-- `Conv(M̃)` (p. 5): the measures `∑_{μ ∈ s} p_μ μ` with `s ⊆ M̃` finite, `p_μ > 0`, `∑ p_μ = 1`. -/
def conv {n : ℕ} (S : Set (Measure (SDEState n))) : Set (Measure (SDEState n)) :=
  {π | ∃ (s : Finset (Measure (SDEState n))) (p : Measure (SDEState n) → ℝ≥0),
    (↑s : Set (Measure (SDEState n))) ⊆ S ∧ (∀ μ ∈ s, 0 < p μ) ∧ ∑ μ ∈ s, p μ = 1 ∧
      π = ∑ μ ∈ s, (p μ : ℝ≥0∞) • μ}

/-- The Lyapunov exponent `λᵢ(μ) = ∫ (fᵢ(x) − σᵢᵢ gᵢ²(x)/2) μ(dx)` (p. 5). -/
noncomputable def lyap {n : ℕ} (C : Coeffs n) (i : Fin n) (μ : Measure (SDEState n)) : ℝ :=
  ∫ x, (C.f i x - C.sig i i * C.g i x ^ 2 / 2) ∂μ

/-- The first two terms of the bracket of (1.2):
`∑ᵢ cᵢxᵢfᵢ(x)/(1 + cᵀx) − ½ ∑ᵢⱼ σᵢⱼcᵢcⱼxᵢxⱼgᵢ(x)gⱼ(x)/(1 + cᵀx)²`. -/
noncomputable def cBracket {n : ℕ} (C : Coeffs n) (c x : SDEState n) : ℝ :=
  (∑ i, c i * x i * C.f i x) / (1 + ∑ i, c i * x i)
    - (1 / 2) * (∑ i, ∑ j, C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x)
      / (1 + ∑ i, c i * x i) ^ 2

/-- Assumption 1.1 (p. 4), with `c` and `γ_b` of part (3) as parameters. The `lim sup < 0` of (1.2)
is written as: the bracket is `≤ −ε` on `{x ∈ ℝⁿ₊ : ‖x‖ ≥ R}` for some `ε > 0` and `R`. -/
def Assumption11 {n : ℕ} (C : Coeffs n) (c : SDEState n) (γb : ℝ) : Prop :=
  (∀ x ∈ orthant n, (Matrix.of fun i j => C.g i x * C.g j x * C.sig i j).PosDef) ∧
  (∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) ∧
  c ∈ openOrthant n ∧ 0 < γb ∧
  ∃ ε > 0, ∃ R : ℝ, ∀ x ∈ orthant n, R ≤ l1 x →
    cBracket C c x + γb * (1 + ∑ i, (|C.f i x| + C.g i x ^ 2)) ≤ -ε

/-- The bracket of (3.3)/(3.5):
`cBracket + γ_b + δ₀ ∑ᵢ (2|fᵢ(x)| + gᵢ²(x)) + 3δ₀ ∑ᵢⱼ |gᵢ(x)gⱼ(x)σᵢⱼ|`. -/
noncomputable def bracket35 {n : ℕ} (C : Coeffs n) (c : SDEState n) (γb δ₀ : ℝ)
    (x : SDEState n) : ℝ :=
  cBracket C c x + γb + δ₀ * ∑ i, (2 * |C.f i x| + C.g i x ^ 2)
    + 3 * δ₀ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|

/-- `M` of (3.1): the bracket of (1.2) is negative whenever `x ∈ ℝⁿ₊`, `‖x‖ ≥ M`. -/
def IsRadiusM {n : ℕ} (C : Coeffs n) (c : SDEState n) (γb M : ℝ) : Prop :=
  ∀ x ∈ orthant n, M ≤ l1 x →
    cBracket C c x + γb * (1 + ∑ i, (|C.f i x| + C.g i x ^ 2)) < 0

/-- `δ₀ ∈ (0, γ_b/2)` with (3.2): `3δ₀ ∑ᵢⱼ |gᵢgⱼσᵢⱼ| + δ₀ ∑ᵢ gᵢ² ≤ γ_b ∑ᵢ gᵢ²` on `ℝⁿ₊`. -/
def IsDelta0 {n : ℕ} (C : Coeffs n) (γb δ₀ : ℝ) : Prop :=
  0 < δ₀ ∧ δ₀ < γb / 2 ∧ ∀ x ∈ orthant n,
    3 * δ₀ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| + δ₀ * ∑ i, C.g i x ^ 2
      ≤ γb * ∑ i, C.g i x ^ 2

/-- `H` of (3.5): the supremum of `bracket35` over `ℝⁿ₊`. -/
noncomputable def Hconst {n : ℕ} (C : Coeffs n) (c : SDEState n) (γb δ₀ : ℝ) : ℝ :=
  sSup ((bracket35 C c γb δ₀) '' orthant n)

/-- `V(x) = (1 + cᵀx) / ∏ᵢ xᵢ^{pᵢ}` of (3.4). -/
noncomputable def Vfun {n : ℕ} (c p x : SDEState n) : ℝ :=
  (1 + ∑ i, c i * x i) / ∏ i, x i ^ p i

end StochKolmogorov.Classify


