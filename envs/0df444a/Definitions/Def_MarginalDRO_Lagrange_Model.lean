-- Prove2me | Definitions.Def_MarginalDRO_Lagrange_Model
-- name    : MarginalDRO_Lagrange_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:51.764987+00:00
-- url     : https://prove2.me/theorems/107390b9-12f5-4365-9cd0-034bb68614ad
-- title:
--   §3.1–3.3, pp. 11–17 — the Fréchet class Γ(µ1,…,µn), couplings Γ(µ,ν), 𝒫(𝒳) and Π_iν, Z(c) = max_{x∈𝒳} cᵀx, the Lagrangian, the quantile F⁻¹ and the objective of (8)
-- statement:
--   This file sets up the **marginal distribution model** of Chen, Ma, Natarajan, Simchi-Levi and Yan for a linear optimization problem over a finite feasible set with random objective coefficients.
--
--   Fix $n \in \mathbb N$, a nonempty finite set $\mathcal X \subset \mathbb R^n$ and probability measures $\mu_1,\dots,\mu_n$ on $\mathbb R$.
--
--   1. **Coordinate projections.** $\mathcal X_i := \{x_i : x \in \mathcal X\}$, a finite subset of $\mathbb R$.
--   2. **Optimal value.** For $c \in \mathbb R^n$,
--   $$Z(c) := \max_{x \in \mathcal X} \sum_{i=1}^n c_i x_i .$$
--   3. **Fréchet class.** $\Gamma(\mu_1,\dots,\mu_n)$ is the set of probability measures $\theta$ on $\mathbb R^n$ whose $i$-th one-dimensional marginal (the image of $\theta$ under $c \mapsto c_i$) equals $\mu_i$ for every $i$.
--   4. **Couplings.** For laws $\mu,\nu$ on $\mathbb R$, $\Gamma(\mu,\nu)$ is the set of probability measures on $\mathbb R \times \mathbb R$ with first marginal $\mu$ and second marginal $\nu$. The value of a coupling $\gamma$ is $E_{(c,x)\sim\gamma}[c\,x] = \int c\,x\,d\gamma$.
--   5. **Distributions on $\mathcal X$.** $\mathcal P(\mathcal X)$ is the standard simplex of probability vectors $\nu = (\nu(x))_{x \in \mathcal X}$. Its $i$-th projection is the law of $x_i$ under $x \sim \nu$:
--   $$\Pi_i\nu := \sum_{x \in \mathcal X} \nu(x)\,\delta_{x_i}.$$
--   6. **Lagrangian.** For functions $\psi_1,\dots,\psi_n : \mathbb R \to \mathbb R$ and $\nu \in \mathcal P(\mathcal X)$,
--   $$L(\{\psi_i\}_i, \nu) := \sum_{i=1}^n \Big( \sum_{x \in \mathcal X} \nu(x)\,\psi_i(x_i) + \int \max_{a \in \mathcal X_i} \{ c\,a - \psi_i(a) \}\, d\mu_i(c) \Big).$$
--   The first inner term is $\int \psi_i\, d\Pi_i\nu$; only the values of $\psi_i$ on $\mathcal X_i$ enter.
--   7. **Quantile.** $F_\mu^{-1}(t) := \inf\{x : F_\mu(x) > t\}$, where $F_\mu(x) = \mu((-\infty,x])$.
--   8. **Coupling supremum.** $\sup_{\gamma \in \Gamma(\mu,\nu)} E_\gamma[c\,x]$.
--   9. **The objective of (8).**
--   $$\sum_{i=1}^n \sum_{a \in \mathcal X_i} a \int_{\Pi_i\nu((-\infty,a))}^{\Pi_i\nu((-\infty,a])} F_{\mu_i}^{-1}(t)\,dt .$$
--
--   These objects are shared by every statement of the mission: the worst-case expected optimal value $\max_{\theta \in \Gamma(\mu_1,\dots,\mu_n)} E_\theta Z$ and its primal and dual reformulations.
--
--   **Formalization Note** $\mathcal X$ is a `Finset`; $\mathcal P(\mathcal X)$ is `stdSimplex ℝ 𝒳` (for finite $\mathcal X$ the weak-* topology is the Euclidean one). The paper's $\psi_i : \mathcal X_i \to \mathbb R$ is encoded as a function on $\mathbb R$ of which only the values on $\mathcal X_i$ are used. The page writes the lower limit of (8) as $\Pi_i\nu((-\infty, x_i - e_i])$ with $x_i - e_i$ the predecessor of $x_i$ in $\mathcal X_i$; since $\mathcal X_i$ is finite this equals $\Pi_i\nu((-\infty, x_i))$. The real infimum defining the quantile takes Lean's default value $0$ when $t \notin (0,1)$ (the page sets $F^{-1}(1) = +\infty$); this concerns only a Lebesgue-null set of $[0,1]$. The coupling supremum is a real `sSup` and is used only where the set is nonempty and bounded above.
-- source:
--   Chen, Ma, Natarajan, Simchi-Levi & Yan, preprint (2018), pp. 5, 11–17: eqs. (4)–(5), Definition 1, Γ and 𝒫(𝒳) (pp. 11–12), Lemma 1 quantile (p. 14), (Lagrangian) (p. 14), x_i − e_i and eq. (8) (p. 17)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MarginalDRO.Lagrange

variable {n : ℕ}

/-- The coordinate projection `𝒳_i := {x_i : x ∈ 𝒳}` of a finite feasible set `𝒳 ⊂ ℝⁿ`. -/
noncomputable def proj (𝒳 : Finset (Fin n → ℝ)) (i : Fin n) : Finset ℝ :=
  𝒳.image (fun x => x i)

/-- The optimal value `Z(c) := max_{x ∈ 𝒳} cᵀx` of the linear problem over a nonempty finite
set `𝒳` (eq. (4), p. 5). -/
noncomputable def Z (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (c : Fin n → ℝ) : ℝ :=
  𝒳.sup' h𝒳 (fun x => ∑ i, c i * x i)

/-- The Fréchet class `Γ(µ_1,…,µ_n)`: probability measures on `ℝⁿ` whose `i`-th one-dimensional
marginal is `µ_i` for every `i` (pp. 11–12). -/
def frechetClass (μ : Fin n → Measure ℝ) : Set (Measure (Fin n → ℝ)) :=
  {θ | IsProbabilityMeasure θ ∧ ∀ i, θ.map (fun c => c i) = μ i}

/-- The couplings `Γ(µ, ν)` of two laws on `ℝ`: probability measures on `ℝ × ℝ` with first
marginal `µ` and second marginal `ν`. -/
def couplings (μ ν : Measure ℝ) : Set (Measure (ℝ × ℝ)) :=
  {γ | IsProbabilityMeasure γ ∧ γ.map Prod.fst = μ ∧ γ.map Prod.snd = ν}

/-- For a probability vector `ν` on the finite set `𝒳`, the `i`-th projection `Π_iν`: the law on
`ℝ` of the coordinate `x_i` when `x ∼ ν` (Definition 1, p. 11). -/
noncomputable def margMeasure (𝒳 : Finset (Fin n → ℝ)) (ν : 𝒳 → ℝ) (i : Fin n) : Measure ℝ :=
  ∑ x : 𝒳, ENNReal.ofReal (ν x) • Measure.dirac ((x : Fin n → ℝ) i)

/-- The conjugate term `max_{x_i ∈ 𝒳_i} {c x_i − ψ_i(x_i)}` of the Lagrangian; only the values of
`ψi` on `𝒳_i` enter. -/
noncomputable def conj (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψi : ℝ → ℝ) (i : Fin n)
    (c : ℝ) : ℝ :=
  (proj 𝒳 i).sup' (h𝒳.image _) (fun a => c * a - ψi a)

/-- The Lagrangian (p. 14)
`L({ψ_i}, ν) = Σ_i (∫ ψ_i dΠ_iν + ∫ max_{x_i ∈ 𝒳_i} {c x_i − ψ_i(x_i)} dµ_i(c))`,
with `∫ ψ_i dΠ_iν` written as the finite sum `Σ_{x ∈ 𝒳} ν(x) ψ_i(x_i)`. -/
noncomputable def lagrangian (μ : Fin n → Measure ℝ) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ψ : Fin n → ℝ → ℝ) (ν : 𝒳 → ℝ) : ℝ :=
  ∑ i, ((∑ x : 𝒳, ν x * ψ i ((x : Fin n → ℝ) i)) + ∫ c, conj 𝒳 h𝒳 (ψ i) i c ∂(μ i))

/-- The quantile function `F_µ^{-1}(t) := inf {x : F_µ(x) > t}` (p. 14). Outside `(0, 1)` the
real infimum takes Lean's junk value `0`; this only affects a Lebesgue-null set of `t ∈ [0, 1]`. -/
noncomputable def quantile (μ : Measure ℝ) (t : ℝ) : ℝ :=
  sInf {x | t < cdf μ x}

/-- The supremum of the coupling value `sup_{γ ∈ Γ(µ, ν)} E_γ[c x]`. Used only where the set is
nonempty and bounded above (finite-mean `µ`, finitely supported `ν`). -/
noncomputable def couplingValue (μ ν : Measure ℝ) : ℝ :=
  sSup {s | ∃ γ ∈ couplings μ ν, s = ∫ p, p.1 * p.2 ∂γ}

/-- The objective of eq. (8), p. 17:
`Σ_i Σ_{x_i ∈ 𝒳_i} x_i ∫_{Π_iν((−∞, x_i − e_i])}^{Π_iν((−∞, x_i])} F_{µ_i}^{-1}(t) dt`,
where `Π_iν((−∞, x_i − e_i]) = Π_iν((−∞, x_i))` because `x_i − e_i` is the predecessor of `x_i`
in the finite set `𝒳_i`. -/
noncomputable def quantileForm (μ : Fin n → Measure ℝ) (𝒳 : Finset (Fin n → ℝ)) (ν : 𝒳 → ℝ) : ℝ :=
  ∑ i, ∑ a ∈ proj 𝒳 i, a *
    ∫ t in ((margMeasure 𝒳 ν i) (Set.Iio a)).toReal..((margMeasure 𝒳 ν i) (Set.Iic a)).toReal,
      quantile (μ i) t

end MarginalDRO.Lagrange


