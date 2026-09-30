-- Prove2me | Definitions.Def_MultistageStochastic_Distortion
-- name    : MultistageStochastic_Distortion
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-23T20:22:13.30799+00:00
-- url     : https://prove2.me/theorems/cd84b55a-e4b4-4e38-b2c5-a704e0f9b94b
-- title:
--   Distortion risk functionals: distortion densities, R_σ, the dual constraint Z ≼ σ, uniform variables and conjugates
-- statement:
--   This file adds to the risk-functional layer of mission II (risk functionals, Value-at-Risk,
--   Average Value-at-Risk, $L^\infty$ membership, atomless spaces, Kusuoka measures) the notions
--   Sections 3.2 to 3.4 need for **distortion risk functionals**.
--
--   **Distortion functions** (Definition 3.6). A distortion function, or distortion density, is a
--   nonnegative, nondecreasing function $\sigma:[0,1)\to[0,\infty)$ with $\int_0^1\sigma(u)\,du=1$.
--   The **distortion risk functional** with density $\sigma$ is
--
--   $$
--   \mathcal R_\sigma(Y)\;:=\;\int_0^1\sigma(u)\,G_Y^{-1}(u)\,du\;=\;\int_0^1\sigma(u)\,\mathsf{V@R}_u(Y)\,du ,
--   \tag{3.7}
--   $$
--
--   with $\mathsf{V@R}_u$ the Value-at-Risk (lower quantile) of Definition 3.3. The Average
--   Value-at-Risk is the case $\sigma_\alpha=(1-\alpha)^{-1}\mathbf 1_{[\alpha,1)}$, (3.10).
--
--   **The dual constraint** (3.16). A random variable $Z$ is dominated by $\sigma$, written
--   $Z\preccurlyeq\sigma$, when $Z\in L^1$, $\mathbb E(Z)=1$ and
--
--   $$
--   \mathsf{AV@R}_\alpha(Z)\;\le\;\frac{1}{1-\alpha}\int_\alpha^1\sigma(u)\,du\qquad\text{for all }\alpha\in[0,1).
--   $$
--
--   **Uniform variables** (footnote 2, p. 99). $U:\Omega\to\mathbb R$ is uniformly distributed on
--   $[0,1]$ when $P(U\le u)=u$ for all $u\in[0,1]$.
--
--   **Conjugates** (footnote 6, p. 111). For $h:\mathbb R\to\mathbb R$, $h^*(s)=\sup_y\,(s\,y-h(y))$,
--   valued in $(-\infty,+\infty]$. A measurable $h$ is *admissible* for $\sigma$ when $h^*(\sigma(u))$
--   is finite for almost every level, $u\mapsto h^*(\sigma(u))$ is integrable on $(0,1)$, and
--   $\int_0^1h^*(\sigma(u))\,du\le 0$, which is the constraint of (3.24).
--
--   **Formalization Note** $\sigma$ is carried as a function on $\mathbb R$ whose values outside
--   $[0,1)$ play no role; its integrability on $(0,1)$ is part of the definition so that the
--   normalisation is a genuine integral rather than the value $0$ that Lean assigns to a
--   non-integrable one. Both integrals in (3.7) and in the normalisation run over the open interval,
--   which removes the level $0$, where the source's formula for the Value-at-Risk is not meaningful,
--   without changing any value. The source writes the constraint of (3.16) for $\alpha\in[0,1]$;
--   at $\alpha=1$ the right-hand side is $0/0$ and is meant as the limit $\sigma(1^-)$, and since both
--   sides are the limits of the $\alpha<1$ case, the constraint at $\alpha=1$ is implied and is not
--   restated. The conjugate takes values in the extended reals so that no supremum is replaced by
--   a junk value; admissibility then requires it to be finite where it is integrated.
-- source:
--   Georg Ch. Pflug and Alois Pichler, Multistage Stochastic Optimization, Springer 2014, https://doi.org/10.1007/978-3-319-08843-3 — Section 3.2, printed p. 99 (PDF p. 112): Definition 3.6 (distortion risk functional) with (3.7), and footnote 2 (uniformly distributed); Section 3.3.2, printed p. 106 (PDF p. 119): the relation Z ≼ σ, (3.16); Section 3.4, printed p. 111 (PDF p. 124): the constraint of (3.24) and footnote 6 (the conjugate function h*).

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional

open MeasureTheory
open scoped ENNReal

namespace MultistageStochastic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Definition 3.6: a **distortion function** (distortion density) is a nonnegative, nondecreasing
function `σ : [0, 1) → [0, ∞)` with `∫₀¹ σ(u) du = 1`.  It is carried here as a function on `ℝ`
whose values outside `[0, 1)` are irrelevant; integrability on `(0, 1)` is stated so that the
normalisation is a genuine integral.  Pflug and Pichler, *Multistage Stochastic Optimization*,
§3.2, p. 99. -/
def IsDistortionFunction (σ : ℝ → ℝ) : Prop :=
  (∀ u ∈ Set.Ico (0 : ℝ) 1, 0 ≤ σ u) ∧ MonotoneOn σ (Set.Ico 0 1) ∧
    IntegrableOn σ (Set.Ioo 0 1) ∧ ∫ u in Set.Ioo (0 : ℝ) 1, σ u = 1

/-- The **distortion risk functional** (3.7), `R_σ(Y) := ∫₀¹ σ(u) G_Y⁻¹(u) du = ∫₀¹ σ(u) V@R_u(Y) du`,
with the Value-at-Risk of Definition 3.3.  The integral is over the open interval, which excludes
the level `0`, where the Value-at-Risk is not given by the source's formula.  Pflug and Pichler,
§3.2, p. 99. -/
noncomputable def distortionFunctional (P : Measure Ω) (σ : ℝ → ℝ) (Y : Ω → ℝ) : ℝ :=
  ∫ u in Set.Ioo (0 : ℝ) 1, σ u * valueAtRisk P Y u

/-- The binary relation `Z ≼ σ` of (3.16), the constraint set of the dual representation (3.15):
`Z` is integrable, `E(Z) = 1`, and `AV@R_α(Z) ≤ (1-α)⁻¹ ∫_α¹ σ(u) du` for every level `α ∈ [0, 1)`.
The source writes the last condition for `α ∈ [0, 1]`; at `α = 1` both sides are limits of the
`α < 1` case, so the constraint there is implied.  Pflug and Pichler, §3.3.2, p. 106. -/
def DominatedByDistortion (P : Measure Ω) (σ : ℝ → ℝ) (Z : Ω → ℝ) : Prop :=
  Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧
    ∀ α : ℝ, 0 ≤ α → α < 1 →
      averageValueAtRisk P Z α ≤ (1 - α)⁻¹ * ∫ u in Set.Ioo α 1, σ u

/-- A random variable `U : Ω → ℝ` is **uniformly distributed** on `[0, 1]` when
`P(U ≤ u) = u` for every `u ∈ [0, 1]`.  Pflug and Pichler, §3.2, p. 99, footnote 2. -/
def IsUniform (P : Measure Ω) (U : Ω → ℝ) : Prop :=
  Measurable U ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1, P {ω | U ω ≤ u} = ENNReal.ofReal u

/-- The **conjugate** (Legendre transform) `h*(s) = sup_y (s·y − h(y))` of a function `h : ℝ → ℝ`,
valued in the extended reals since the supremum may be `+∞`.  Pflug and Pichler, §3.4, p. 111,
footnote 6. -/
noncomputable def conjugate (h : ℝ → ℝ) (s : ℝ) : EReal :=
  ⨆ y : ℝ, ((s * y - h y : ℝ) : EReal)

/-- The constraint set of Theorem 3.22 (3.24): measurable `h : ℝ → ℝ` whose conjugate is finite
along `σ` for almost every level, with `u ↦ h*(σ(u))` integrable on `(0, 1)` and
`∫₀¹ h*(σ(u)) du ≤ 0`.  Pflug and Pichler, §3.4, p. 111. -/
def IsAdmissibleConjugate (σ : ℝ → ℝ) (h : ℝ → ℝ) : Prop :=
  Measurable h ∧
    (∀ᵐ u ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), conjugate h (σ u) ≠ ⊤) ∧
    IntegrableOn (fun u => (conjugate h (σ u)).toReal) (Set.Ioo 0 1) ∧
    ∫ u in Set.Ioo (0 : ℝ) 1, (conjugate h (σ u)).toReal ≤ 0

end MultistageStochastic


