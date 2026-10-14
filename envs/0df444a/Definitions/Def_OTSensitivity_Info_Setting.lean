-- Prove2me | Definitions.Def_OTSensitivity_Info_Setting
-- name    : OTSensitivity_Info_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:23.131198+00:00
-- url     : https://prove2.me/theorems/9dda6608-4663-47c2-a512-b2f72e9c8a22
-- title:
--   Cost assumption, 𝕄^K (18), conditional distributions and ξ^K(Y, X|𝓕) (Definition 1, (16))
-- statement:
--   This file fixes the objects of §3.1 of Borgonovo, Figalli, Plischke and Savaré.
--
--   Let $(\Omega,\mathcal B,\mathbb P)$ be a probability space, $\mathsf X$ and $\mathsf Y$ Polish spaces with their Borel σ-algebras $\mathscr B(\mathsf X)$, $\mathscr B(\mathsf Y)$, and $X:\Omega\to\mathsf X$, $Y:\Omega\to\mathsf Y$ random variables with laws $\mu$ and $\nu$. Let $K(\nu,\nu')$ be the optimal-transport cost (1) of a cost function $\mathsf k:\mathsf Y\times\mathsf Y\to[0,+\infty]$, the infimum of $\iint \mathsf k\,d\pi$ over couplings $\pi$ of $\nu$ and $\nu'$.
--
--   1. **Cost assumption** (standing assumption of §3.1). $\mathsf k$ is continuous and $\mathsf k(y,y')=0$ if and only if $y=y'$.
--   2. **The maximal value** (18). $$\mathbb M^K[Y]=\int_{\mathsf Y^2}\mathsf k(y,y')\,d\nu(y)\,d\nu(y').$$
--   3. **Conditional distributions.** For a σ-algebra $\mathcal F$ on $\mathsf X$, a family $(\nu^{\mathcal F}_x)_{x\in\mathsf X}$ of probability measures on $\mathsf Y$ is a version of the conditional distribution of $Y$ given $(X,\mathcal F)$ if $x\mapsto\nu^{\mathcal F}_x(B)$ is $\mathcal F$-measurable for every Borel $B\subseteq\mathsf Y$ and
--   $$\mathbb P(X\in A,\ Y\in B)=\int_A \nu^{\mathcal F}_x(B)\,d\mu(x)\qquad\text{for all }A\in\mathcal F,\ B\in\mathscr B(\mathsf Y).$$
--   4. **The sensitivity measure** (Definition 1, (16)). $$\xi^K(Y,X\mid\mathcal F)=\int_{\mathsf X}K(\nu,\nu^{\mathcal F}_x)\,d\mu(x).$$ When $\mathcal F=\mathscr B(\mathsf X)$ it is written $\xi^K(Y,X)$.
--   5. **Functional dependence** (Theorem 5). $Y$ is functionally dependent on $(X,\mathcal F)$ if $Y=f(X)$ $\mathbb P$-a.s. for some $\mathcal F$-measurable $f:\mathsf X\to\mathsf Y$.
--
--   These are the objects every statement of the mission is about: $\xi^K(Y,X\mid\mathcal F)$ is the expected optimal-transport cost of moving the marginal law of $Y$ to its conditional law given the information $\mathcal F$ on $X$.
--
--   **Formalization Note** The paper's supports $\mathsf X\subseteq\mathbb R^{n_X}$, $\mathsf Y\subseteq\mathbb R^{n_Y}$ are closed sets, hence Polish; the theorems of the mission assume Polish spaces with Borel σ-algebras. Costs, $\mathbb M^K$ and $\xi^K$ take values in $[0,+\infty]$ (`ℝ≥0∞`), so infinite values are allowed as on the page. $K$ is the published platform definition `RWPI.SqrtLasso.transportCost`; its first argument is the marginal $\nu$ and its second the conditional law, and $\mathsf k(y,y')$ has $y\sim\nu$. The conditional distribution is not chosen: `IsCondDistrib` characterizes every version (a Markov kernel with the two properties above), and `xi` takes the version as an argument; every theorem quantifies over all versions. $\mathbb M^K$ is an iterated lower Lebesgue integral. The σ-algebra $\mathcal F$ is an arbitrary `MeasurableSpace` on $\mathsf X$; the theorems add $\mathcal F\subseteq\mathscr B(\mathsf X)$.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), §3.1 standing assumption, Definition 1 (16) and (18), p. 9; Theorem 5, p. 10; (67), p. 35

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSensitivity.Info

/-- `κ` is a version of the conditional distribution `(ν^𝓕_x)_x` of `Y` given `(X, 𝓕)`
(Definition 1, p. 9; the defining property is the one used in (67), p. 35): `κ` is a Markov kernel,
`x ↦ κ x B` is `𝓕`-measurable for every Borel `B`, and
`P(X ∈ A, Y ∈ B) = ∫_A κ x B dµ(x)` for `A ∈ 𝓕`, `B` Borel, where `µ` is the law of `X`. -/
def IsCondDistrib {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω] [m𝓧 : MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    (P : Measure Ω) (X : Ω → 𝓧) (Y : Ω → 𝓨) (F : MeasurableSpace 𝓧) (κ : @Kernel 𝓧 𝓨 m𝓧 _) :
    Prop :=
  IsMarkovKernel κ ∧
    (∀ B : Set 𝓨, MeasurableSet B → Measurable[F] (fun x => κ x B)) ∧
    (∀ A : Set 𝓧, MeasurableSet[F] A → ∀ B : Set 𝓨, MeasurableSet B →
      P (X ⁻¹' A ∩ Y ⁻¹' B) = ∫⁻ x in A, κ x B ∂(@Measure.map Ω 𝓧 _ m𝓧 X P))

end OTSensitivity.Info


