-- Prove2me | Definitions.Def_OTSensitivity_Consist_Setting
-- name    : OTSensitivity_Consist_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:33:54.198348+00:00
-- url     : https://prove2.me/theorems/373439c7-203c-4eeb-aa9e-db9758bf20a3
-- title:
--   Cost assumption, $\mathbb M^K$ (18), conditional distributions and $\xi^K(Y,X\mid\mathcal F)$ (Definition 1, (16))
-- statement:
--   Let $\mathsf X$ and $\mathsf Y$ be measurable spaces (in the statements of this mission they are Polish spaces with their Borel $\sigma$-algebras), let $(\Omega,\mathcal B,\mathbb P)$ be a probability space, and let $X:\Omega\to\mathsf X$, $Y:\Omega\to\mathsf Y$ be random variables with laws $\mu=X_\sharp\mathbb P$ and $\nu=Y_\sharp\mathbb P$. This module fixes the objects of §3.1 of the paper.
--
--   1. **Cost.** A cost $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ satisfies the standing assumption of §3.1 if it is continuous and vanishes exactly on the diagonal: $k(y,y')=0\iff y=y'$.
--   2. **The quantity $\mathbb M^K$** of (18): $$\mathbb M^K[Y]=\int_{\mathsf Y}\int_{\mathsf Y}k(y,y')\,d\nu(y')\,d\nu(y).$$
--   3. **Conditional distributions.** For a $\sigma$-algebra $\mathcal F$ on $\mathsf X$, a Markov kernel $x\mapsto\nu^{\mathcal F}_x$ from $\mathsf X$ to $\mathsf Y$ is a version of the conditional distribution of $Y$ given $(X,\mathcal F)$ if $x\mapsto\nu^{\mathcal F}_x(B)$ is $\mathcal F$-measurable for every measurable $B\subseteq\mathsf Y$ and $$\mathbb P(X\in A,\;Y\in B)=\int_A\nu^{\mathcal F}_x(B)\,d\mu(x)\qquad\text{for all }A\in\mathcal F\text{ and measurable }B.$$
--   4. **The OT-based sensitivity measure** (Definition 1, (16)): with $K$ the optimal transport cost of (1), $$\xi^K(Y,X\mid\mathcal F)=\int_{\mathsf X}K(\nu,\nu^{\mathcal F}_x)\,d\mu(x).$$ When $\mathcal F$ is the Borel $\sigma$-algebra it is written $\xi^K(Y,X)$.
--   5. **Functional dependence**: $Y=f(X)$ $\mathbb P$-a.e. for some $\mathcal F$-measurable $f:\mathsf X\to\mathsf Y$.
--
--   These are the objects in terms of which every result of the paper on OT-based sensitivity measures is stated.
--
--   **Formalization Note** Values of $K$, $\xi^K$ and $\mathbb M^K$ live in $[0,+\infty]$ (`ℝ≥0∞`), so $+\infty$ is allowed as in the paper. $K$ is the published definition `RWPI.SqrtLasso.transportCost k ν ν'` (infimum over probability couplings of $\int k\,d\pi$, first argument the marginal law). The conditional distribution is not chosen: `xi` takes a kernel as an argument, and every theorem quantifies over all kernels satisfying the characterizing predicate `IsCondDistrib`; the kernel, $\mu$ and the integral are taken with respect to the ambient $\sigma$-algebra of $\mathsf X$, and $\mathcal F$ enters only through the measurability requirements. The integral in (16) is the lower Lebesgue integral.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), §3.1, Definition 1, (16) and (18), p. 9; Theorem 5, p. 10

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSensitivity.Consist

/-- Standing cost assumption of §3.1 (p. 9): `k : 𝒴 × 𝒴 → [0, +∞]` is continuous and
`k y y' = 0 ↔ y = y'`. -/
def IsCost {𝒴 : Type*} [TopologicalSpace 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞) : Prop :=
  Continuous (Function.uncurry k) ∧ ∀ y y', k y y' = 0 ↔ y = y'

/-- `𝕄^K[Y] = ∫∫ k(y, y') dν(y) dν(y')`, equation (18), p. 9. -/
noncomputable def MK {𝒴 : Type*} [MeasurableSpace 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞) (ν : Measure 𝒴) : ℝ≥0∞ :=
  ∫⁻ y, ∫⁻ y', k y y' ∂ν ∂ν

/-- `κ` is a version of the conditional distribution of `Y` given `(X, 𝓕)` (the `ν^𝓕_x` of
Definition 1, p. 9): a Markov kernel, `𝓕`-measurable in `x`, and
`P(X ∈ A, Y ∈ B) = ∫_A κ x B dμ(x)` for every `A ∈ 𝓕` and every measurable `B`, where `μ = X♯P`.
The kernel, the law `μ = X♯P` and the integral are taken with respect to the ambient σ-algebra
`m𝒳` of `𝒳` (written explicitly, so that the argument `F` is not used as an instance); `F` enters
only through `Measurable[F]` and `MeasurableSet[F]`. -/
def IsCondDistrib {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω] [m𝒳 : MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (P : Measure Ω) (X : Ω → 𝒳) (Y : Ω → 𝒴) (F : MeasurableSpace 𝒳)
    (κ : @Kernel 𝒳 𝒴 m𝒳 _) : Prop :=
  IsMarkovKernel κ ∧
  (∀ B : Set 𝒴, MeasurableSet B → Measurable[F] (fun x => κ x B)) ∧
  (∀ A : Set 𝒳, MeasurableSet[F] A → ∀ B : Set 𝒴, MeasurableSet B →
    P (X ⁻¹' A ∩ Y ⁻¹' B) =
      @lintegral 𝒳 m𝒳 (@Measure.restrict 𝒳 m𝒳 (@Measure.map Ω 𝒳 _ m𝒳 X P) A) (fun x => κ x B))

/-- The OT-based global sensitivity measure, Definition 1, (16), p. 9:
`ξ^K(Y, X | 𝓕) = ∫ K(ν, ν^𝓕_x) dμ(x)` with `ν = Y♯P`, `μ = X♯P` and `κ` a version of the
conditional distribution of `Y` given `(X, 𝓕)` (supplied separately via `IsCondDistrib`). -/
noncomputable def xi {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (P : Measure Ω) (X : Ω → 𝒳) (Y : Ω → 𝒴) (κ : Kernel 𝒳 𝒴) : ℝ≥0∞ :=
  ∫⁻ x, RWPI.SqrtLasso.transportCost k (P.map Y) (κ x) ∂(P.map X)

/-- `Y = f(X)` `P`-a.e. for some `𝓕`-measurable `f` (Theorem 5, p. 10). -/
def IsFunctionallyDependent {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒴]
    (P : Measure Ω) (X : Ω → 𝒳) (Y : Ω → 𝒴) (F : MeasurableSpace 𝒳) : Prop :=
  ∃ f : 𝒳 → 𝒴, Measurable[F] f ∧ Y =ᵐ[P] f ∘ X

end OTSensitivity.Consist


