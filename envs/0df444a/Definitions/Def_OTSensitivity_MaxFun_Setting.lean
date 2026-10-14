-- Prove2me | Definitions.Def_OTSensitivity_MaxFun_Setting
-- name    : OTSensitivity_MaxFun_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:06:58.103371+00:00
-- url     : https://prove2.me/theorems/99d2dc26-b26b-45e6-9d7c-0a98a302357c
-- title:
--   Cost assumption, 𝕄^K (18), conditional distributions and ξ^K(Y, X|𝓕) (Definition 1, (16))
-- statement:
--   This file fixes the objects of §3.1 of Borgonovo, Figalli, Plischke and Savaré.
--
--   Let $(\Omega,\mathcal B,P)$ be a probability space, let $\mathsf X$ and $\mathsf Y$ be Polish spaces with their Borel $\sigma$-algebras, and let $X:\Omega\to\mathsf X$ (the input) and $Y:\Omega\to\mathsf Y$ (the output) be measurable. Write $\mu=X_\sharp P$ and $\nu=Y_\sharp P$ for their laws. For probability measures $\nu,\nu'$ on $\mathsf Y$, $K(\nu,\nu')=\inf_{\pi\in\Pi(\nu,\nu')}\iint k(y,y')\,d\pi(y,y')$ is the optimal transport cost (1) with cost $k$.
--
--   1. **Cost assumption** (standing assumption of §3.1). A cost $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ is admissible if it is continuous and vanishes exactly on the diagonal: $k(y,y')=0\iff y=y'$.
--   2. **The quantity $\mathbb M^K$** (18). For a measure $\nu$ on $\mathsf Y$,
--   $$\mathbb M^K[\nu]=\int_{\mathsf Y}\int_{\mathsf Y}k(y,y')\,d\nu(y')\,d\nu(y),$$
--   which for $\nu$ the law of $Y$ is $\mathbb E[k(Y,Y')]$ with $Y'$ an independent copy of $Y$.
--   3. **Conditional distribution given $(X,\mathcal F)$.** For a sub-$\sigma$-algebra $\mathcal F$ of the Borel sets of $\mathsf X$, a Markov kernel $x\mapsto\nu^{\mathcal F}_x$ from $\mathsf X$ to $\mathsf Y$ is a version of the conditional distribution of $Y$ given $(X,\mathcal F)$ if $x\mapsto\nu^{\mathcal F}_x(B)$ is $\mathcal F$-measurable for every Borel $B\subseteq\mathsf Y$ and
--   $$P(X\in A,\ Y\in B)=\int_A\nu^{\mathcal F}_x(B)\,d\mu(x)\qquad\text{for all }A\in\mathcal F,\ B\text{ Borel}.$$
--   4. **OT-based sensitivity measure** (Definition 1, (16)). Given such a version,
--   $$\xi^K(Y,X\mid\mathcal F)=\int_{\mathsf X}K(\nu,\nu^{\mathcal F}_x)\,d\mu(x).$$
--   When $\mathcal F$ is the whole Borel $\sigma$-algebra it is written $\xi^K(Y,X)$.
--   5. **Functional dependence.** $Y$ is functionally dependent on $(X,\mathcal F)$ if $Y=f(X)$ $P$-almost surely for some $\mathcal F$-measurable map $f:\mathsf X\to\mathsf Y$.
--
--   These are the objects in which the paper's zero-independence (Proposition 3) and max-functionality (Theorem 5) properties are stated.
--
--   **Formalization Note** The paper takes $\mathsf X\subseteq\mathbb R^{n_X}$ and $\mathsf Y\subseteq\mathbb R^{n_Y}$ as supports of the laws; those closed sets are Polish, so the Polish setting contains the paper's. All values ($k$, $K$, $\mathbb M^K$, $\xi^K$) lie in $[0,+\infty]$ (`ℝ≥0∞`), so $+\infty$ is allowed as on the page. $K$ is the published definition `RWPI.SqrtLasso.transportCost`, whose first argument is the marginal $\nu$ and whose cost is evaluated as $k(y,y')$ with $y\sim\nu$. The conditional distribution is not a chosen object: `IsCondDistrib` characterizes every version by its defining property, and the theorems quantify over every version. In `IsCondDistrib` the kernel, its Markov property and the law $\mu$ in the defining identity are all taken with respect to $\mathcal F$ itself (so $\mu$ there is the law of $X$ restricted to $\mathcal F$); for $A\in\mathcal F$ and the $\mathcal F$-measurable integrand $x\mapsto\nu^{\mathcal F}_x(B)$ this is the same integral as against the Borel law of $X$, and the predicate can only hold when $X$ is $\mathcal F$-measurable as a map into $(\mathsf X,\mathcal F)$, which follows from measurability of $X$ when $\mathcal F$ is contained in the Borel sets. The inclusion $\mathcal F\subseteq\mathcal B(\mathsf X)$ is a hypothesis of each theorem, not part of the predicate. The value of $\xi^K$ is computed from the given version `κ`, with respect to the σ-algebra on $\mathsf X$ that the kernel carries.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), §3.1 standing assumption, Definition 1 and (16), (18), p. 9; Theorem 5, p. 10

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSensitivity.MaxFun

/-- The standing assumption of §3.1 (p. 9) on the cost `k : 𝒴 × 𝒴 → [0, +∞]`: `k` is continuous
(`ℝ≥0∞` carries its order topology, so the value `+∞` is allowed) and `k y y' = 0 ↔ y = y'`. -/
def IsCost {𝒴 : Type*} [TopologicalSpace 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞) : Prop :=
  Continuous (Function.uncurry k) ∧ ∀ y y', k y y' = 0 ↔ y = y'

/-- `𝕄^K[Y] = E[k(Y, Y')] = ∫∫ k(y, y') dν(y) dν(y')` for the law `ν` of `Y` and an independent
replica `Y'`, (18), p. 9. -/
noncomputable def MK {𝒴 : Type*} [MeasurableSpace 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞) (ν : Measure 𝒴) : ℝ≥0∞ :=
  ∫⁻ y, ∫⁻ y', k y y' ∂ν ∂ν

/-- `κ` is a version of the conditional distribution `(ν^𝓕_x)_{x ∈ 𝒳}` of `Y` given `(X, 𝓕)`:
a Markov kernel, `𝓕`-measurable in `x`, with `P(X ∈ A, Y ∈ B) = ∫_A κ x B dµ(x)` for every
`A ∈ 𝓕` and every measurable `B`, where `µ` is the law of `X`. -/
def IsCondDistrib {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (P : Measure Ω) (X : Ω → 𝒳) (Y : Ω → 𝒴) (F : MeasurableSpace 𝒳) (κ : Kernel 𝒳 𝒴) : Prop :=
  IsMarkovKernel κ ∧
  (∀ B : Set 𝒴, MeasurableSet B → Measurable[F] (fun x => κ x B)) ∧
  ∀ A : Set 𝒳, MeasurableSet[F] A → ∀ B : Set 𝒴, MeasurableSet B →
    P (X ⁻¹' A ∩ Y ⁻¹' B) = ∫⁻ x in A, κ x B ∂(P.map X)

/-- The OT-based global sensitivity measure `ξ^K(Y, X | 𝓕) = ∫_𝒳 K(ν, ν^𝓕_x) dµ(x)` of
Definition 1, (16), p. 9, computed from a version `κ` of the conditional distribution; `ν` is the
law of `Y`, `µ` the law of `X`, and `K` the optimal transport cost (1) with cost `k`. -/
noncomputable def xi {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (P : Measure Ω) (X : Ω → 𝒳) (Y : Ω → 𝒴) (κ : Kernel 𝒳 𝒴) : ℝ≥0∞ :=
  ∫⁻ x, RWPI.SqrtLasso.transportCost k (P.map Y) (κ x) ∂(P.map X)

/-- `Y` is functionally dependent on `(X, 𝓕)`: `Y = f(X)` `P`-a.e. for some `𝓕`-measurable
`f : 𝒳 → 𝒴` (Theorem 5, p. 10). -/
def IsFunctionallyDependent {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒴]
    (P : Measure Ω) (X : Ω → 𝒳) (Y : Ω → 𝒴) (F : MeasurableSpace 𝒳) : Prop :=
  ∃ f : 𝒳 → 𝒴, Measurable[F] f ∧ Y =ᵐ[P] f ∘ X

end OTSensitivity.MaxFun


