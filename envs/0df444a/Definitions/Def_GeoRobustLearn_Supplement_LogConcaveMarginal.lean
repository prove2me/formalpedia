-- Prove2me | Definitions.Def_GeoRobustLearn_Supplement_LogConcaveMarginal
-- name    : GeoRobustLearn_Supplement_LogConcaveMarginal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:38:02.48121+00:00
-- url     : https://prove2.me/theorems/c63ac3e5-e641-4f2b-b5df-9cc82decadeb
-- title:
--   Isotropic $\alpha$-strongly log-concave marginals, Gaussian convolution $H_t$, and the polynomial approximation assumption (22)
-- statement:
--   Let $\gamma_n$ be the standard Gaussian measure on $\mathbb R^n$.
--
--   1. A probability measure $\mu$ on $\mathbb R^d$ is **isotropic $\alpha$-strongly log-concave** if it has density $e^{-V}$ with respect to Lebesgue measure, where $V:\mathbb R^d\to\mathbb R\cup\{+\infty\}$ and $V(x)-\alpha\|x\|_2^2/2$ is convex, its mean is $0$ and its covariance is $I_d$: $\int\langle x,u\rangle\langle x,v\rangle\,d\mu(x)=\langle u,v\rangle$ for all $u,v$.
--   2. The **Gaussian convolution operator** is
--   $$H_tF(z)=\mathbb E_{g\sim\gamma_n}F(z+\sqrt t\,g),\qquad t>0.$$
--   3. The **polynomial approximation assumption (22)** says: for every $n$, every $\kappa>0$, every $\kappa$-strongly log-concave probability measure $\nu$ on $\mathbb R^n$, every bounded measurable $F$, every $t>0$ and every integer $k\ge0$,
--   $$\inf_{\deg p\le k}\|p-H_tF\|_{L_2(\nu)}^2\le\|F\|_\infty^2(1+\kappa t)^{-(k+1)}.$$
--
--   These are the setting and the explicit hypothesis of the paper's conditional extension (Theorem A.2) beyond Gaussian marginals. The paper uses (22) as an assumption, not as a known theorem (Remark A.1).
--
--   **Formalization Note** The strong log-concavity of $\mu$ is the published `LCAntiConc.IsStronglyLogConcave` (extended-valued $V$). In (22) the measures $\nu$ are taken in the published sense `PolySampIso.IsStronglyLogConcaveOn ν Set.univ κ` (real-valued potential, full support); this is implied by (22) for extended-valued potentials, and the paper applies (22) only to such full-support measures. $\|F\|_\infty$ is any pointwise bound $M\ge|F|$, $\deg$ is total degree, and the squared $L_2$ distance and its infimum are computed in $[0,\infty]$. The condition $\int\|x\|^2d\mu<\infty$ is included; it follows from strong log-concavity.
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Appendix A, p.43 (PDF p.43): the marginal μ, the operator H_t, assumption (22)

import Definitions.Def_GeoLipLearn_Agnostic_Gaussian
import Definitions.Def_PolySampIso_LogConcave
import Definitions.Def_LCAntiConc_IsStronglyLogConcave

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn.Supplement

open GeoLipLearn.Agnostic

/-!
# Isotropic strongly log-concave marginals, Gaussian convolution, and assumption (22)

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I: Agnostically Learning Adversarially
Robust Classifiers*, manuscript of November 3, 2026 (sha256 8cbf3f52…), Appendix A, p.43: the
marginal `μ`, the Gaussian convolution operator `H_t`, and the polynomial approximation
assumption (22).

**Formalization Note.**
* `ℝ^n` is the published `GeoLipLearn.Agnostic.Space n` (`EuclideanSpace ℝ (Fin n)`) and `γ_n` the
  published `GeoLipLearn.Agnostic.gaussian n`.
* The marginal `μ` is `α`-strongly log-concave in the published sense
  `LCAntiConc.IsStronglyLogConcave`: density `e^{−V}` with `V : ℝ^d → ℝ ∪ {+∞}` and
  `V − α‖·‖²/2` convex (the density may vanish outside a convex set).
* In (22) the measures `ν` are `κ`-strongly log-concave in the published sense
  `PolySampIso.IsStronglyLogConcaveOn ν Set.univ κ`: density `e^{−U}` with `U` real-valued on all of
  `ℝ^n` and `U − (κ/2)‖·‖²` convex. This is the subclass of full-support measures, so the assumption
  as stated here is implied by (22) read with extended-valued potentials, and also equals (22) read
  with real-valued potentials.
* `‖F‖_∞` is replaced by an arbitrary bound `M` with `|F| ≤ M` everywhere (equivalently the sup
  norm); `deg p ≤ k` is total degree; the squared `L_2(ν)` distance and its infimum are computed in
  `ℝ≥0∞`, so no value is a junk default.
-/

/-- `μ` is an isotropic `α`-strongly log-concave probability measure on `ℝ^d` (Appendix A, p.43):
a probability measure with density `e^{−V}`, `V − α‖·‖²/2` convex, mean zero and covariance `I_d`.

**Formalization Note.** The conjunct `∫ ‖x‖² dμ < ∞` is implied by strong log-concavity (all
moments are finite) and only makes the mean and covariance integrals visibly non-junk. Covariance
`I_d` is `∫ ⟪x,u⟫⟪x,v⟫ dμ = ⟪u,v⟫` for all `u, v` (with mean zero). -/
def IsotropicSLC {d : ℕ} (α : ℝ) (μ : Measure (Space d)) : Prop :=
  IsProbabilityMeasure μ ∧ LCAntiConc.IsStronglyLogConcave α μ ∧
    Integrable (fun x : Space d => ‖x‖ ^ 2) μ ∧ ∫ x, x ∂μ = 0 ∧
    ∀ u v : Space d, ∫ x, inner ℝ x u * inner ℝ x v ∂μ = inner ℝ u v

/-- The Gaussian convolution operator of Appendix A, p.43:
`H_t F(z) = E_{g∼γ_n} F(z + √t g)`.

**Formalization Note.** This is the heat semigroup, not the Ornstein–Uhlenbeck operator `ou` of the
main body (no contraction factor). It is only applied to bounded measurable `F`, for which the
Bochner integral is a genuine expectation. -/
noncomputable def gaussConv {n : ℕ} (t : ℝ) (F : Space n → ℝ) (z : Space n) : ℝ :=
  ∫ g, F (z + Real.sqrt t • g) ∂gaussian n

/-- The polynomial approximation assumption (22) (Appendix A, p.43): for every dimension `n`, every
`κ`-strongly log-concave probability measure `ν` on `ℝ^n`, every bounded measurable `F`, every
`t > 0` and every integer `k ≥ 0`,
`inf_{deg p ≤ k} ‖p − H_t F‖²_{L_2(ν)} ≤ ‖F‖²_∞ (1 + κt)^{−(k+1)}`.

**Formalization Note.** A closed proposition, used as a hypothesis of Theorem A.2, never as an
axiom. `‖F‖_∞` is any bound `M` on `|F|`; `κ > 0` ("strongly"); see the module note for the class
of `ν`. -/
def PolyApprox22 : Prop :=
  ∀ (n : ℕ) (ν : Measure (Space n)) (κ : ℝ), 0 < κ → IsProbabilityMeasure ν →
    PolySampIso.IsStronglyLogConcaveOn ν Set.univ κ →
    ∀ (F : Space n → ℝ) (M : ℝ), Measurable F → (∀ z, |F z| ≤ M) →
    ∀ t : ℝ, 0 < t → ∀ k : ℕ,
      (⨅ (p : MvPolynomial (Fin n) ℝ) (_ : p.totalDegree ≤ k),
        ∫⁻ z, ENNReal.ofReal ((MvPolynomial.eval (fun i => z i) p - gaussConv t F z) ^ 2) ∂ν)
        ≤ ENNReal.ofReal (M ^ 2 * (1 + κ * t) ^ (-((k : ℝ) + 1)))

end GeoRobustLearn.Supplement


