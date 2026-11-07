-- Prove2me | Definitions.Def_MixScale_Profile
-- name    : MixScale_Profile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:06:45.16521+00:00
-- url     : https://prove2.me/theorems/ec92ee9a-64ad-4e87-85e5-8ad928c179a7
-- title:
--   Effective ordinary-smooth profile (Definition A.1), radial characteristic functions, and the rate functions $\ell_q$, $E_{\mathrm{free}}$, $E_{\mathrm{eq}}$, $\mathcal L_q$
-- statement:
--   A **profile specification** consists of a function $\chi$ on $[0,\infty)$, a function $H$ on $[-h_0,h_0]$, constants $q,\alpha,c_0,\lambda,z_0,C_\chi,h_0$, known bounds $H_b(i)$ on the derivatives $H^{(i)}$ for $i\le 3$, and two constants $\mathrm{evalC},\mathrm{evalD}$ that price an evaluation of $H$.
--
--   The profile is **effective** if all the constants are positive, $|\chi(z)|\le C_\chi(1+z)^{-q}$ for $z\ge0$, $H\in C^3[-h_0,h_0]$, $H(0)=1$, $H'(0)=-\lambda$, $|H^{(i)}|\le H_b(i)$ on $[-h_0,h_0]$, and
--
--   $$\chi(z)=c_0z^{-q}H(z^{-\alpha})\quad(z\ge z_0),\qquad z_0^{-\alpha}\le h_0/4 .$$
--
--   The function $\chi$ is a **radial characteristic function in dimension $d$** if $t\mapsto\chi(\|t\|)$ is the characteristic function of a probability measure on $\mathbb R^d$.
--
--   The rates are $\ell_q(\gamma)=\log(e/\gamma)$ if $q=1$ and $1$ otherwise; $E_{\mathrm{free}}=2(q+\alpha)-\min(q,1)$; $E_{\mathrm{eq}}=2q-\min(q,1)$; and $\mathcal L_q(R)=\log(2+R)$ if $q=1$ and $1$ otherwise. There are two weight classes, unrestricted and equal.
--
--   These objects describe how the leading Fourier decay and its first relative correction enter every result of the mission.
--
--   **Formalization Note** Item 3 of Definition A.1 (evaluation of $H,H',H''$ to error $\eta$ in time polynomial in $\eta^{-1}$, with fixed degree) is not a property of the functions: it is realised by the adversarial oracle of `MixScale.Machine`, whose query with tolerance $\eta$ costs $\lceil\mathrm{evalC}(1+1/\eta)^{\mathrm{evalD}}\rceil$. The radial condition is per dimension and is assumed for the dimension at hand.
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Definition A.1, p.13 (PDF p.15); §1.1, p.2; (4), p.3; Theorem 1.1, p.3; (72), p.35; §A.1, p.14

import Mathlib

open MeasureTheory

namespace MixScale

/-!
# The known radial profile (Definition A.1) and the rate functions of Theorem 1.1

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*,
STOC 2027 submission manuscript (sha256 5277f95e…7c6c). Definition A.1, p.13 (PDF p.15); the
profile convention of §1.1, p.2 (PDF p.4); (4), p.3 (PDF p.5); the rates of Theorem 1.1, p.3,
(72), p.35 (PDF p.37), and `ℒ_q` of §A.1, p.14 (PDF p.16).

**Formalization Note.**
* A profile specification `ProfileSpec` bundles the profile `χ`, its tail factor `H`, the
  constants `q, α, c₀, λ, z₀, C_χ, h₀`, the known bounds `Hb i` on `|H^{(i)}|` over `[−h₀, h₀]`
  (`i = 0, 1, 2, 3`) and the two constants `evalC`, `evalD` of the evaluation cost. The functions
  are total `ℝ → ℝ`; only `χ` on `[0, ∞)` and `H` on `[−h₀, h₀]` are ever used.
* `IsEffectiveProfile` is items 1–2 of Definition A.1, with `h₀ > 0` (the interval `[−h₀, h₀]`
  is nondegenerate) and `evalC > 0`. Item 3 (evaluation of `H, H′, H″` to error `η` in time
  polynomial in `η⁻¹`, with fixed degree) is not a property of the functions: it is realised by
  the adversarial oracle of `MixScale.Machine`, whose query with tolerance `η` costs
  `⌈evalC · (1 + 1/η)^evalD⌉`.
* The characteristic-function condition "`t ↦ χ(‖t‖)` is a characteristic function" is per
  dimension: `IsRadialCF χ d`. Theorems assume it for the dimension at hand.
* Derivatives of `H` are `iteratedDerivWithin` on `[−h₀, h₀]`; real powers are `Real.rpow`.
-/

/-- A fixed profile specification: the profile `χ`, the exact tail factor `H`, the constants of
Definition A.1 items 1–2, the known derivative bounds `Hb i ≥ sup_{[−h₀,h₀]} |H^{(i)}|`, and the
evaluation-cost constants `evalC`, `evalD` of item 3. -/
structure ProfileSpec where
  /-- The radial profile `χ : [0, ∞) → ℝ` (values on negative reals are never used). -/
  χ : ℝ → ℝ
  /-- The exact tail factor `H` on `[−h₀, h₀]`. -/
  H : ℝ → ℝ
  /-- The leading Fourier decay order `q`. -/
  q : ℝ
  /-- The order `α` of the first relative correction. -/
  α : ℝ
  /-- The leading constant `c₀`. -/
  c0 : ℝ
  /-- The correction constant `λ = −H′(0)`. -/
  lam : ℝ
  /-- The threshold `z₀` of the exact representation. -/
  z0 : ℝ
  /-- The constant `C_χ` of the global bound. -/
  Cχ : ℝ
  /-- The half-width `h₀` of the domain of `H`. -/
  h0 : ℝ
  /-- Known bounds on `|H|, |H′|, |H″|, |H‴|` over `[−h₀, h₀]`. -/
  Hb : Fin 4 → ℝ
  /-- Evaluation cost constant: a query with tolerance `η` costs `⌈evalC (1 + 1/η)^evalD⌉`. -/
  evalC : ℝ
  /-- Evaluation cost degree. -/
  evalD : ℕ

/-- `t ↦ χ(‖t‖)` is the characteristic function of a probability measure on `ℝ^d`. -/
def IsRadialCF (χ : ℝ → ℝ) (d : ℕ) : Prop :=
  ∃ ν : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure ν ∧
    ∀ t, charFun ν t = (χ ‖t‖ : ℂ)

/-- Definition A.1, items 1–2 (Effective ordinary-smooth profile), p.13:
1. `q, α, c₀, λ, z₀, C_χ > 0` and `|χ(z)| ≤ C_χ (1 + z)^{−q}` for `z ≥ 0`;
2. `H ∈ C³[−h₀, h₀]`, `H(0) = 1`, `H′(0) = −λ`, `|H^{(i)}| ≤ Hb i` on `[−h₀, h₀]` for `i ≤ 3`,
   `χ(z) = c₀ z^{−q} H(z^{−α})` for `z ≥ z₀`, and `z₀^{−α} ≤ h₀/4`.
Also `h₀ > 0` and `evalC > 0`. -/
def IsEffectiveProfile (S : ProfileSpec) : Prop :=
  0 < S.q ∧ 0 < S.α ∧ 0 < S.c0 ∧ 0 < S.lam ∧ 0 < S.z0 ∧ 0 < S.Cχ ∧ 0 < S.h0 ∧ 0 < S.evalC ∧
  (∀ z : ℝ, 0 ≤ z → |S.χ z| ≤ S.Cχ * (1 + z) ^ (-S.q)) ∧
  ContDiffOn ℝ 3 S.H (Set.Icc (-S.h0) S.h0) ∧
  S.H 0 = 1 ∧
  derivWithin S.H (Set.Icc (-S.h0) S.h0) 0 = -S.lam ∧
  (∀ i : Fin 4, ∀ u ∈ Set.Icc (-S.h0) S.h0,
    |iteratedDerivWithin (i : ℕ) S.H (Set.Icc (-S.h0) S.h0) u| ≤ S.Hb i) ∧
  (∀ z : ℝ, S.z0 ≤ z → S.χ z = S.c0 * z ^ (-S.q) * S.H (z ^ (-S.α))) ∧
  S.z0 ^ (-S.α) ≤ S.h0 / 4

/-- `ℓ_q(γ) = log(e/γ)` if `q = 1`, and `1` otherwise (Theorem 1.1, p.3; (72), p.35). -/
noncomputable def ellq (q γ : ℝ) : ℝ :=
  if q = 1 then Real.log (Real.exp 1 / γ) else 1

/-- `E_free = 2(q + α) − min(q, 1)` (Theorem 1.1; `E_{q,α}` of (72)). -/
noncomputable def Efree (q α : ℝ) : ℝ := 2 * (q + α) - min q 1

/-- `E_eq = 2q − min(q, 1)` (Theorem 1.1). -/
noncomputable def Eeq (q : ℝ) : ℝ := 2 * q - min q 1

/-- `ℒ_q(R) = log(2 + R)` if `q = 1`, and `1` otherwise (§A.1, p.14; Lemma C.1, p.21). This is a
different function from `ℓ_q`. -/
noncomputable def Lcal (q R : ℝ) : ℝ :=
  if q = 1 then Real.log (2 + R) else 1

/-- The two weight classes of §1.1: unrestricted weights and equal weights. -/
inductive WeightClass where
  | free
  | eq
  deriving DecidableEq

/-- The sample exponent `E_W` of the weight class `W`. -/
noncomputable def WeightClass.exponent : WeightClass → ℝ → ℝ → ℝ
  | .free, q, α => Efree q α
  | .eq, q, _ => Eeq q

end MixScale


