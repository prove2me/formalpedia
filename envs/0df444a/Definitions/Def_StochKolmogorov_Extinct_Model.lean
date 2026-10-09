-- Prove2me | Definitions.Def_StochKolmogorov_Extinct_Model
-- name    : StochKolmogorov_Extinct_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:47.11341+00:00
-- url     : https://prove2.me/theorems/7f60399c-c9a5-4a15-908b-8df8c8b50f6a
-- title:
--   §1.1 and §3 — Kolmogorov SDE and standing model
-- statement:
--   The model has $n\ge1$ populations with nonnegative abundance vector $x$. For each species $i$, $f_i(x)$ is its per-capita drift, $g_i(x)$ its noise intensity, and $E=\Gamma^\top B$ is correlated environmental Brownian noise with covariance $\Sigma=\Gamma^\top\Gamma$. The stochastic equation is
--
--   $$dX_i(t)=X_i(t)f_i(X(t))\,dt+X_i(t)g_i(X(t))\,dE_i(t).$$
--
--   The module defines the nonnegative orthant and its interior, the transition and occupation measures, invariant and ergodic measures, finite convex combinations of boundary ergodic measures, and the invasion rate $\lambda_i(\mu)=\int(f_i-\sigma_{ii}g_i^2/2)\,d\mu$. It also records Assumption 1.1, the Lyapunov functions and constants in (3.1)–(3.5).
--
--   These shared objects give each theorem the same stochastic system and the same boundary-measure convention.
--
--   **Formalization Note** Coordinates use `Fin n` with zero-based indexing and the paper's norm is the $\ell^1$ norm. Coefficients are extended off the orthant by reading them at the componentwise positive part; solutions from the orthant remain there. The strict limit superior in (1.2) is represented by an equivalent eventual $-\varepsilon$ bound. Ergodicity means extremality among invariant probability measures. The integral defining $\lambda_i$ is a real Bochner integral; its integrability follows from the paper's Lemma 3.3.
--
--   **Moderation note** The radius constant in (3.1) is positive. The freely chosen exponent in (3.2) is taken below one, as used in the paper’s Appendix A proof of Lemma 3.1.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, §1.1, pp. 3–5, and §3, pp. 13–14, (1.1), (1.2), Assumption 1.1, (3.1)–(3.5)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SolvesBrownianSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

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

/-- `mu` is an invariant probability measure of `X` on `ℝⁿ₊`. -/
def IsInvariant {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (mu : Measure (SDEState n)) : Prop :=
  IsProbabilityMeasure mu ∧ mu ((orthant n)ᶜ) = 0 ∧
    ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      ∫⁻ x, trans P X t x A ∂mu = mu A

/-- `mu` is an ergodic invariant probability measure: an extreme point of the convex set of
invariant probability measures. -/
def IsErgodic {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (mu : Measure (SDEState n)) : Prop :=
  IsInvariant P X mu ∧
    ∀ ν₁ ν₂ : Measure (SDEState n), IsInvariant P X ν₁ → IsInvariant P X ν₂ →
      ∀ a : ℝ≥0, 0 < a → a < 1 →
        mu = (a : ℝ≥0∞) • ν₁ + ((1 - a : ℝ≥0) : ℝ≥0∞) • ν₂ → ν₁ = mu

/-- `M`, the ergodic invariant probability measures of `X` supported on `∂ℝⁿ₊` (p. 5). -/
def bdryErgodic {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Set (Measure (SDEState n)) :=
  {mu | IsErgodic P X mu ∧ mu (openOrthant n) = 0}

/-- `Conv(M̃)` (p. 5): the measures `∑_{mu ∈ s} p_mu mu` with `s ⊆ M̃` finite, `p_mu > 0`, `∑ p_mu = 1`. -/
def conv {n : ℕ} (S : Set (Measure (SDEState n))) : Set (Measure (SDEState n)) :=
  {π | ∃ (s : Finset (Measure (SDEState n))) (p : Measure (SDEState n) → ℝ≥0),
    (↑s : Set (Measure (SDEState n))) ⊆ S ∧ (∀ mu ∈ s, 0 < p mu) ∧ ∑ mu ∈ s, p mu = 1 ∧
      π = ∑ mu ∈ s, (p mu : ℝ≥0∞) • mu}

/-- The Lyapunov exponent `λᵢ(mu) = ∫ (fᵢ(x) − σᵢᵢ gᵢ²(x)/2) mu(dx)` (p. 5). -/
noncomputable def lyap {n : ℕ} (C : Coeffs n) (i : Fin n) (mu : Measure (SDEState n)) : ℝ :=
  ∫ x, (C.f i x - C.sig i i * C.g i x ^ 2 / 2) ∂mu

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

/-- `M > 0` of (3.1): the bracket of (1.2) is negative whenever `x ∈ ℝⁿ₊`, `‖x‖ ≥ M`. -/
def IsRadiusM {n : ℕ} (C : Coeffs n) (c : SDEState n) (γb M : ℝ) : Prop :=
  0 < M ∧ ∀ x ∈ orthant n, M ≤ l1 x →
    cBracket C c x + γb * (1 + ∑ i, (|C.f i x| + C.g i x ^ 2)) < 0

/-- `δ₀ ∈ (0, min(γ_b/2,1))` with (3.2). The proof of Lemma 3.1 on p. 29
uses the freely chosen `δ₀ < 1`. -/
def IsDelta0 {n : ℕ} (C : Coeffs n) (γb δ₀ : ℝ) : Prop :=
  0 < δ₀ ∧ δ₀ < min (γb / 2) 1 ∧ ∀ x ∈ orthant n,
    3 * δ₀ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| + δ₀ * ∑ i, C.g i x ^ 2
      ≤ γb * ∑ i, C.g i x ^ 2

/-- `H` of (3.5): the supremum of `bracket35` over `ℝⁿ₊`. -/
noncomputable def Hconst {n : ℕ} (C : Coeffs n) (c : SDEState n) (γb δ₀ : ℝ) : ℝ :=
  sSup ((bracket35 C c γb δ₀) '' orthant n)

/-- `V(x) = (1 + cᵀx) / ∏ᵢ xᵢ^{pᵢ}` of (3.4). -/
noncomputable def Vfun {n : ℕ} (c p x : SDEState n) : ℝ :=
  (1 + ∑ i, c i * x i) / ∏ i, x i ^ p i

end StochKolmogorov.Extinct


