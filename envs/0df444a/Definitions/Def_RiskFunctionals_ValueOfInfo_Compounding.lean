-- Prove2me | Definitions.Def_RiskFunctionals_ValueOfInfo_Compounding
-- name    : RiskFunctionals_ValueOfInfo_Compounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:39.28634+00:00
-- url     : https://prove2.me/theorems/73f09be3-ec3b-4d59-9cd6-3e060ae20c75
-- title:
--   Compound linear, compound convex and compound concave probability functionals (Definition 2.11)
-- statement:
--   A **version-independent probability functional** $\mathcal R$ assigns a real number $\mathcal R\{G\}$ to a distribution $G$ on $\mathbb R$ (so $\mathcal R(Y)=\mathcal R\{G_Y\}$ depends on a random variable $Y$ only through its law). Let $K(\cdot\mid v)$, $v\in\mathbb R$, be a Markov kernel — a family of distributions on $\mathbb R$ indexed by a real parameter, measurable in $v$ — and let $G$ be a distribution on $\mathbb R$. The **compound distribution** is
--   $$(K\circ G)(B)=\int K(B\mid v)\,dG(v).$$
--   Then $\mathcal R$ is
--
--   1. **compound linear** if $\mathcal R\{K\circ G\}=\int \mathcal R\{K(\cdot\mid v)\}\,dG(v)$,
--   2. **compound convex** if $\mathcal R\{K\circ G\}\le\int \mathcal R\{K(\cdot\mid v)\}\,dG(v)$,
--   3. **compound concave** if $\mathcal R\{K\circ G\}\ge\int \mathcal R\{K(\cdot\mid v)\}\,dG(v)$,
--
--   for all such $K$ and $G$ for which the integral on the right exists. These properties are relative to the **domain** $\mathcal D=\operatorname{dom}\mathcal R$ of distributions on which $\mathcal R$ is meaningful (the book's Example 2.13: expected utility is "compound linear on the family of distributions w.r.t. which $U$ is integrable"): $\mathcal R$ is compound linear (convex, concave) **on $\mathcal D$** if the relation holds whenever $K(\cdot\mid v)\in\mathcal D$ for $G$-almost every $v$ and $K\circ G\in\mathcal D$.
--
--   These properties express how a functional of distributions interacts with mixing; they are what lets a functional be applied to conditional distributions and averaged, as in the comparison of $\mathcal R(Y)$ with $\mathbb E[\mathcal R(Y\mid\mathcal F_1)]$ and in the martingale properties of the optimality and clairvoyant processes of multi-stage decision problems.
--
--   **Formalization Note** $\mathcal R$ is a map `Measure ℝ → ℝ`; it is only ever evaluated at probability measures, and its values elsewhere are irrelevant. The book lets $\mathcal R$ take values in $\overline{\mathbb R}$; here it is real-valued on its domain $\mathcal D$ (a parameter `𝒟 : Set (Measure ℝ)`; `Set.univ` gives the domain-free notion; for the expectation take the distributions with a finite mean), and each defining (in)equality is required only for those $G$ and $K$ for which $v\mapsto\mathcal R\{K(\cdot\mid v)\}$ is $G$-integrable, so that the Bochner integral is the genuine integral. The mixing parameter ranges over $\mathbb R$, as in the book's definition of compounding (p. 20). $K\circ G$ is Mathlib's `K ∘ₘ G` (`Measure.bind`).
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 33, Definition 2.11 (compound distribution: p. 20, Eq. (1.21))

import Mathlib

namespace RiskFunctionals.ValueOfInfo

open MeasureTheory ProbabilityTheory

/-- Compound linearity (Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific
2007, p. 33, Definition 2.11(i)). A version-independent probability functional is a map `ℛ` on
distributions on `ℝ`, meaningful on its domain `𝒟` (`dom ℛ`, p. 34; Example 2.13 calls expected
utility "compound linear on the family of distributions w.r.t. which `U` is integrable"); it is
only ever evaluated at probability measures. `ℛ` is compound linear on `𝒟` if for every
distribution `G` on `ℝ` and every Markov kernel `K(·|v)` from `ℝ` to `ℝ` (p. 20, §1.2.4: "a family
of distribution functions indexed with a real parameter") with `K(·|v) ∈ 𝒟` for `G`-almost every
`v` and with the compound distribution `K ∘ G = ∫ K(·|v) dG(v)` (1.21) in `𝒟`, one has
`ℛ{K ∘ G} = ∫ ℛ{K(·|v)} dG(v)` whenever the right-hand integral exists (`v ↦ ℛ{K(·|v)}` is
`G`-integrable). With `𝒟 = Set.univ` this is compound linearity on all distributions. -/
def CompoundLinear (𝒟 : Set (Measure ℝ)) (ℛ : Measure ℝ → ℝ) : Prop :=
  ∀ (G : Measure ℝ), IsProbabilityMeasure G → ∀ (K : Kernel ℝ ℝ), IsMarkovKernel K →
    (∀ᵐ v ∂G, K v ∈ 𝒟) → K ∘ₘ G ∈ 𝒟 →
    Integrable (fun v => ℛ (K v)) G → ℛ (K ∘ₘ G) = ∫ v, ℛ (K v) ∂G

/-- Compound convexity on the domain `𝒟` (p. 33, Definition 2.11(ii)):
`ℛ{K ∘ G} ≤ ∫ ℛ{K(·|v)} dG(v)` for every distribution `G` on `ℝ` and every Markov kernel `K` from
`ℝ` to `ℝ` with `K(·|v) ∈ 𝒟` for `G`-a.e. `v` and `K ∘ G ∈ 𝒟`, for which the right-hand integral
exists. -/
def CompoundConvex (𝒟 : Set (Measure ℝ)) (ℛ : Measure ℝ → ℝ) : Prop :=
  ∀ (G : Measure ℝ), IsProbabilityMeasure G → ∀ (K : Kernel ℝ ℝ), IsMarkovKernel K →
    (∀ᵐ v ∂G, K v ∈ 𝒟) → K ∘ₘ G ∈ 𝒟 →
    Integrable (fun v => ℛ (K v)) G → ℛ (K ∘ₘ G) ≤ ∫ v, ℛ (K v) ∂G

/-- Compound concavity on the domain `𝒟` (p. 33, Definition 2.11(iii)):
`ℛ{K ∘ G} ≥ ∫ ℛ{K(·|v)} dG(v)` for every distribution `G` on `ℝ` and every Markov kernel `K` from
`ℝ` to `ℝ` with `K(·|v) ∈ 𝒟` for `G`-a.e. `v` and `K ∘ G ∈ 𝒟`, for which the right-hand integral
exists. -/
def CompoundConcave (𝒟 : Set (Measure ℝ)) (ℛ : Measure ℝ → ℝ) : Prop :=
  ∀ (G : Measure ℝ), IsProbabilityMeasure G → ∀ (K : Kernel ℝ ℝ), IsMarkovKernel K →
    (∀ᵐ v ∂G, K v ∈ 𝒟) → K ∘ₘ G ∈ 𝒟 →
    Integrable (fun v => ℛ (K v)) G → ∫ v, ℛ (K v) ∂G ≤ ℛ (K ∘ₘ G)

end RiskFunctionals.ValueOfInfo


