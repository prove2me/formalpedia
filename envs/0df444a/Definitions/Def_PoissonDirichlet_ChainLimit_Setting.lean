-- Prove2me | Definitions.Def_PoissonDirichlet_ChainLimit_Setting
-- name    : PoissonDirichlet_ChainLimit_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:53.507975+00:00
-- url     : https://prove2.me/theorems/b784d59d-ca79-4eb4-b195-250dda1f7c30
-- title:
--   Definition 1 and (32), (34), (43), (45): PD(α, θ), Σ_n, ψ_α, Y_n
-- statement:
--   For $0\le\alpha<1$ and $\theta> -\alpha$, let $\tilde Y_n$ be independent beta$(1-\alpha,\theta+n\alpha)$ variables, with beta density proportional to $x^{a-1}(1-x)^{b-1}$ on $(0,1)$. Form the **stick lengths** $\tilde V_1=\tilde Y_1$ and $\tilde V_n=(1-\tilde Y_1)\cdots(1-\tilde Y_{n-1})\tilde Y_n$ for $n\ge2$. The law of their decreasing rearrangement $V_1\ge V_2\ge\cdots$, counting multiplicities, is $\mathrm{PD}(\alpha,\theta)$ (Definition 1).
--
--   For any sequence $v=(v_n)_{n\ge1}$, define the **tail ratio**, the **chain factor**, and the transform function by
--   $$\Sigma_n=\frac{\sum_{j>n}v_j}{v_n},\qquad Y_n=\frac{v_n}{\sum_{j\ge n}v_j},\qquad \psi_\alpha(\lambda)=1+\alpha\int_0^1(1-e^{-\lambda x})x^{-\alpha-1}\,dx.$$
--   Also define the $n$-fold additive convolution $\mu^{*n}$, with $\mu^{*0}=\delta_0$, and $C_{\alpha,\theta}=\Gamma(\theta+1)\Gamma(1-\alpha)^{\theta/\alpha}/\Gamma(\theta/\alpha+1)$.
--
--   These definitions connect the ranked Poisson–Dirichlet frequencies to the tail variables used in Proposition 44.
--
--   **Formalization Note** Sequences use zero-based Lean indices: `v k` is $V_{k+1}$. Ranking uses extended cardinality `Set.encard`, including when infinitely many terms exceed a threshold. The PD law is stated by equality of measurable preimage probabilities, with an almost everywhere measurable random sequence, avoiding `Measure.map`'s fallback on nonmeasurable maps. Real sums and integrals are used only in the parameter ranges stated by the theorems.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 857, Definition 1, (3)–(4); p. 863, (32), (34); p. 865, (43), (45)

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.ChainLimit

/-- The stick-breaking sequence (4), indexed from zero. -/
def stick (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ Finset.range k, (1 - y i)) * y k

/-- The `(k+1)`-st largest value of a nonnegative sequence, with multiplicity.
`encard` prevents an infinite exceedance set from having junk cardinality zero. -/
noncomputable def ranked (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ {i | t < x i}.encard ≤ k}

/-- Definition 1: independent beta factors with the paper's parameterization. -/
def IsStickLaw (α θ : ℝ) (μ : Measure (ℕ → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧ iIndepFun (fun k (y : ℕ → ℝ) => y k) μ ∧
    ∀ k : ℕ, HasLaw (fun y : ℕ → ℝ => y k)
      (betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) μ

/-- Definition 1: the law of the ranked stick lengths. Preimage equality avoids
the zero-measure fallback of `Measure.map` for a nonmeasurable map. -/
def HasPD {Ω : Type*} [MeasurableSpace Ω]
    (α θ : ℝ) (P : Measure Ω) (V : Ω → ℕ → ℝ) : Prop :=
  AEMeasurable V P ∧ ∃ μ : Measure (ℕ → ℝ), IsStickLaw α θ μ ∧
    ∀ s : Set (ℕ → ℝ), MeasurableSet s →
      P (V ⁻¹' s) = μ ((fun y => ranked (stick y)) ⁻¹' s)

/-- (45): `Yseq v k` is `Y_{k+1}=V_{k+1}/(V_{k+1}+V_{k+2}+⋯)`. -/
noncomputable def Yseq (v : ℕ → ℝ) (k : ℕ) : ℝ :=
  v k / ∑' j, v (k + j)

/-- (32): `Sigseq v k` is `Σ_{k+1}=(V_{k+2}+V_{k+3}+⋯)/V_{k+1}`. -/
noncomputable def Sigseq (v : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑' j, v (k + 1 + j)) / v k

/-- (34): `ψ_α(λ)=1+α∫₀¹(1-e^{-λx})x^{-α-1}dx`. -/
noncomputable def psi (α l : ℝ) : ℝ :=
  1 + α * ∫ x in Set.Ioc (0 : ℝ) 1,
    (1 - Real.exp (-l * x)) * x ^ (-α - 1)

/-- The `n`-fold convolution of a real probability law, with `convPow μ 0=δ₀`. -/
noncomputable def convPow (μ : Measure ℝ) (n : ℕ) : Measure ℝ :=
  (fun ν => ν ∗ μ)^[n] (Measure.dirac 0)

/-- The second expression of (43), `C_{α,θ}`. -/
noncomputable def pdConst (α θ : ℝ) : ℝ :=
  Real.Gamma (θ + 1) / Real.Gamma (θ / α + 1) *
    Real.Gamma (1 - α) ^ (θ / α)

end PoissonDirichlet.ChainLimit


