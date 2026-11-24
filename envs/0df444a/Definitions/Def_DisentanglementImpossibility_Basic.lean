-- Prove2me | Definitions.Def_DisentanglementImpossibility_Basic
-- name    : DisentanglementImpossibility_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T07:27:45.654186+00:00
-- url     : https://prove2.me/theorems/1619f544-5a40-46c6-b5a9-395a7ac9895e
-- title:
--   Factorized latent laws and the entangling maps $g$, $h$, $A$, $f$ of Theorem 1
-- statement:
--   Objects of Theorem 1 (Section 3, p. 3) and of its proof (Appendix A, p. 12) in Locatello et al. (2019).
--
--   1. **Factorized latent law.** A latent variable $z=(z_1,\dots,z_d)$ has independent coordinates $z_i\sim\mu_i$, where each $\mu_i$ is a probability measure on $\mathbb{R}$ with a density with respect to Lebesgue measure. Its law $P=\mu_1\otimes\cdots\otimes\mu_d$ therefore has the density $p(z)=\prod_i p(z_i)$. $\operatorname{supp}(z)$ is the support of $P$, the set of points all of whose neighbourhoods have positive probability.
--   2. **The map $g$.** $g_i(v)=P(z_i\le v_i)=F_i(v_i)$, where $F_i$ is the cumulative distribution function of $\mu_i$.
--   3. **Quantiles.** For a law $\nu$ on $\mathbb{R}$ with distribution function $F_\nu$ and $w\in(0,1)$, the quantile is $F_\nu^{-1}(w)=\inf\{x: w\le F_\nu(x)\}$. It is the inverse of $F_\nu$ wherever $F_\nu$ is strictly increasing.
--   4. **The map $h$.** $\psi$ is the standard normal distribution function, $\psi^{-1}$ its quantile function, and $h_i(v)=\psi^{-1}(v_i)$.
--   5. **Reference laws.** The uniform law on $[0,1]^d$ is the product of $d$ copies of Lebesgue measure on $[0,1]$. The standard normal law on $\mathbb{R}^d$ is the product of $d$ copies of $N(0,1)$.
--   6. **Householder matrix.** For $\alpha\in\mathbb{R}$, $v_1=\sqrt\alpha$ and $v_i=\sqrt{(1-\alpha)/(d-1)}$ for $i=2,\dots,d$. The matrix is $A=I_d-2vv^\top$.
--   7. **Entangling map.** For a $d\times d$ matrix $A$, $f(u)=g^{-1}(h^{-1}(A\,h(g(u))))$, that is, $f_i(u)=F_i^{-1}\big(\psi\big((A\,h(g(u)))_i\big)\big)$.
--   8. **Partial derivatives.** $\partial f_i(u)/\partial u_j$ is the derivative at $t=u_j$ of $t\mapsto f_i(u_1,\dots,u_{j-1},t,u_{j+1},\dots,u_d)$. For a map defined on a set $S$, the variable $t$ ranges over those values for which $(u_1,\dots,t,\dots,u_d)\in S$.
--
--   **Formalization Note** Lean's `deriv` and `derivWithin` return $0$ where the derivative does not exist, so a statement that a partial derivative is nonzero also asserts that it exists. The quantile is the infimum of a set of reals. For $w\notin(0,1)$ that set is unbounded below or empty, and the value is a default. Such arguments occur only on null sets. In Lean the first coordinate of the Householder vector has index $0$.
-- source:
--   Locatello, Bauer, Lucic, Rätsch, Gelly, Schölkopf, Bachem, Challenging Common Assumptions in the Unsupervised Learning of Disentangled Representations, ICML 2019, arXiv:1811.12359v4, Section 3 (Theorem 1, p. 3) and Appendix A (Proof of Theorem 1, p. 12)

import Mathlib

/-!
Locatello, Bauer, Lucic, Rätsch, Gelly, Schölkopf and Bachem, *Challenging Common Assumptions in
the Unsupervised Learning of Disentangled Representations*, ICML 2019, arXiv:1811.12359v4:
the factorized latent law of Theorem 1 (Section 3, p. 3) and the maps `g`, `h`, `A`, `f` built in
its proof (Appendix A, p. 12).
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace DisentanglementImpossibility

variable {d : ℕ}

/-- Section 3, Theorem 1 (p. 3): `z ∼ P` admits a density `p(z) = ∏ᵢ p(zᵢ)`. The law is given by
its marginals `μ i`, each a probability measure on `ℝ` with a density (absolutely continuous with
respect to Lebesgue measure); the law of `z` is their product `latentLaw μ`. -/
def IsFactorizedDensity (μ : Fin d → Measure ℝ) : Prop :=
  ∀ i, IsProbabilityMeasure (μ i) ∧ μ i ≪ volume

/-- Section 3, Theorem 1 (p. 3): the law `P` of `z = (z₁, …, z_d)` with independent coordinates
`zᵢ ∼ μ i`, i.e. the product measure. Its support `(latentLaw μ).support` is `supp(z)`. -/
def latentLaw (μ : Fin d → Measure ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi μ

/-- Appendix A (p. 12): the map `g : supp(z) → [0,1]^d`, `gᵢ(v) = P(zᵢ ≤ vᵢ)`, applying the
cumulative distribution function of each marginal to its coordinate. -/
def cdfMap (μ : Fin d → Measure ℝ) (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => cdf (μ i) (v i)

/-- Appendix A (p. 12): the inverse of a cumulative distribution function, used for `g⁻¹` and for
`ψ⁻¹`. For a law `ν` on `ℝ` and `w ∈ (0,1)`, `quantile ν w = inf {x | w ≤ P_ν(X ≤ x)}`; when the
cumulative distribution function is strictly increasing this is its inverse. Values at
`w ∉ (0,1)` are a default and only occur on null sets. -/
def quantile (ν : Measure ℝ) (w : ℝ) : ℝ :=
  sInf {x : ℝ | w ≤ cdf ν x}

/-- Appendix A (p. 12): `ψ`, the cumulative distribution function of the standard normal law. -/
def stdNormalCdf (x : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) x

/-- Appendix A (p. 12): `ψ⁻¹`, the inverse of the standard normal cumulative distribution
function on `(0,1)`. -/
def stdNormalQuantile (w : ℝ) : ℝ :=
  quantile (gaussianReal 0 1) w

/-- Appendix A (p. 12): the map `h`, `hᵢ(v) = ψ⁻¹(vᵢ)`. -/
def gaussMap (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => stdNormalQuantile (v i)

/-- Appendix A (p. 12): the independent `d`-dimensional uniform distribution, the law of `g(z)`:
the product of `d` copies of Lebesgue measure on `[0,1]`. -/
def uniformCube (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => volume.restrict (Set.Icc (0 : ℝ) 1)

/-- Appendix A (p. 12): the `d`-dimensional standard normal distribution, the law of `h(g(z))`:
the product of `d` copies of the standard normal law `N(0,1)`. -/
def stdGaussian (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => gaussianReal 0 1

/-- Appendix A (p. 12): the Householder vector `v` with `v₁ = √α` and `vᵢ = √((1-α)/(d-1))` for
`i = 2, …, d` (the first coordinate is index `0` here). -/
def householderVec (d : ℕ) (α : ℝ) : Fin d → ℝ :=
  fun i => if i.val = 0 then Real.sqrt α else Real.sqrt ((1 - α) / ((d : ℝ) - 1))

/-- Appendix A (p. 12): the Householder matrix `A = I_d - 2 v vᵀ` built from `householderVec`. -/
def householderMat (d : ℕ) (α : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  1 - (2 : ℝ) • Matrix.vecMulVec (householderVec d α) (householderVec d α)

/-- Appendix A (p. 12): the entangling map `f(u) = g⁻¹(h⁻¹(A h(g(u))))` for a matrix `A`:
coordinate `i` of `f(u)` is `quantile (μ i) (ψ((A h(g(u)))ᵢ))`. -/
def entanglingMap (μ : Fin d → Measure ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) :
    Fin d → ℝ :=
  fun i => quantile (μ i) (stdNormalCdf ((A.mulVec (gaussMap (cdfMap μ u))) i))

/-- Section 3, Theorem 1 (p. 3): the partial derivative `∂fᵢ(u)/∂u_j`, the derivative at `u_j` of
`t ↦ fᵢ(u₁, …, t, …, u_d)` (`t` in position `j`). Lean's `deriv` is `0` where this derivative
does not exist, so `partialDeriv f i j u ≠ 0` asserts that it exists and is nonzero. -/
def partialDeriv (f : (Fin d → ℝ) → Fin d → ℝ) (i j : Fin d) (u : Fin d → ℝ) : ℝ :=
  deriv (fun t => f (Function.update u j t) i) (u j)

/-- Section 3, Theorem 1 (p. 3): the partial derivative `∂fᵢ(u)/∂u_j` of a map `f : S → S`
defined on a set `S` (the support `supp(z)`): the derivative at `u_j` of
`t ↦ fᵢ(u₁, …, t, …, u_d)` along those `t` for which `(u₁, …, t, …, u_d) ∈ S`. Lean's
`derivWithin` is `0` where this derivative does not exist (or `u_j` is isolated), so a nonzero
value asserts that it exists and is nonzero. -/
def partialDerivWithin (f : (Fin d → ℝ) → Fin d → ℝ) (S : Set (Fin d → ℝ)) (i j : Fin d)
    (u : Fin d → ℝ) : ℝ :=
  derivWithin (fun t => f (Function.update u j t) i) {t | Function.update u j t ∈ S} (u j)

end DisentanglementImpossibility


