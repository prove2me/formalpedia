-- Prove2me | Definitions.Def_SumReLU_rejection
-- name    : SumReLU_rejection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:21.888645+00:00
-- url     : https://prove2.me/theorems/0affc9e5-dc96-44d0-9423-dbc7dadf597f
-- title:
--   The $(\gamma,v)$-rejection procedure: acceptance probability, $A^{\pm1/2}_{\gamma,v}$, accepted law, $\bar w,\tilde w,\tilde\beta$
-- statement:
--   Fix a unit vector $v\in S^{d-1}$ and $\gamma\in(0,1)$. A covariate $x\in\mathbb R^d$ is accepted with probability
--   $$
--   a_{\gamma,v}(x)=\exp\Big(-\frac{\gamma^{-2}-1}{2}(v\cdot x)^2\Big),
--   $$
--   and $x_\gamma$ denotes $x\sim N(0,I_d)$ conditioned on acceptance. Let $A_{\gamma,v}=I_d-(1-\gamma^2)vv^\top$, with symmetric square root $A^{1/2}_{\gamma,v}z=z-(1-\gamma)(v\cdot z)v$ and inverse $A^{-1/2}_{\gamma,v}x=x+(\gamma^{-1}-1)(v\cdot x)v$. For a weight vector $w$,
--   $$
--   \bar w=w^{\perp v}+\gamma(v\cdot w)v,\qquad \tilde w=\bar w/\|\bar w\|_2,\qquad \tilde\beta=\beta\|\bar w\|_2 .
--   $$
--
--   These objects describe the localization step of the algorithm: after rejection sampling and the change of variables $z=A^{-1/2}_{\gamma,v}x_\gamma$, the data again form a Gaussian sum of ReLUs with parameters $(\tilde\beta,\tilde w)$.
--
--   **Formalization Note** The law of $x_\gamma$ is $N(0,I_d)$ reweighted by $a_{\gamma,v}$ and divided by its own total mass, so the value $\Pr[\text{accept}]=\gamma$ of Fact 3.2 (a cited fact) is not presupposed.
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Fact 3.2, Definition 3.3, Fact 3.4, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_SumReLU_thetaPM

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- The acceptance probability `a_{γ,v}(x) = exp(−((γ^{−2} − 1)/2)(v · x)²)` of the
`(γ, v)`-rejection procedure `RS_{γ,v}`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Fact 3.2, p.13 (PDF p.15). -/
noncomputable def accept {d : ℕ} (γ : ℝ) (v x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.exp (-((γ⁻¹ ^ 2 - 1) / 2) * (inner ℝ v x) ^ 2)

/-- `A_{γ,v}^{1/2} z = z − (1 − γ)(v · z) v`, the symmetric square root of
`A_{γ,v} = I_d − (1 − γ²)vvᵀ` for a unit vector `v` (Fact 3.4, p.13, PDF p.15).

**Formalization Note.** Written as the explicit rank-one update; for unit `v` and `γ > 0` it is the
positive square root of `A_{γ,v}` (it scales `v` by `γ` and fixes `v^⊥`). -/
noncomputable def Ahalf {d : ℕ} (γ : ℝ) (v z : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  z - ((1 - γ) * inner ℝ v z) • v

/-- `A_{γ,v}^{−1/2} x = x + (γ^{−1} − 1)(v · x) v`, the inverse of `A_{γ,v}^{1/2}` for a unit vector
`v` and `γ > 0` (Definition 3.3 and Fact 3.4, p.13, PDF p.15). -/
noncomputable def Ainvhalf {d : ℕ} (γ : ℝ) (v x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  x + ((γ⁻¹ - 1) * inner ℝ v x) • v

/-- **The law of an accepted covariate** `x_γ`: `x ∼ N(0, I_d)` conditioned on being accepted by
`RS_{γ,v}`, i.e. `N(0, I_d)` reweighted by `a_{γ,v}` and normalized by its own total mass.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Fact 3.2 and Definition 3.3, p.13 (PDF p.15): "Let x_γ denote the sample x conditioned on
being accepted by RS_{γ,v}."

**Formalization Note.** The normalization is the reweighted measure's own mass, so the value
`Pr[accept] = γ` of Fact 3.2 (a cited fact) is not presupposed. -/
noncomputable def acceptedLaw {d : ℕ} (γ : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  let μ := (stdGaussian (EuclideanSpace ℝ (Fin d))).withDensity
    (fun x => ENNReal.ofReal (accept γ v x))
  (μ Set.univ)⁻¹ • μ

/-- `w̄ = w^{⊥v} + γ(v · w) v = A_{γ,v}^{1/2} w` (Fact 3.4, item 2, p.13, PDF p.15). -/
noncomputable def wbar {d : ℕ} (γ : ℝ) (v w : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  perp v w + (γ * inner ℝ v w) • v

/-- `w̃ = w̄/‖w̄‖₂`, the hidden weight vector after rejection sampling (Fact 3.4, item 2). -/
noncomputable def wtilde {d : ℕ} (γ : ℝ) (v w : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  normalize (wbar γ v w)

/-- `β̃ = β‖w̄‖₂`, the coefficient after rejection sampling (Fact 3.4, item 2). -/
noncomputable def btilde {d : ℕ} (β γ : ℝ) (v w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  β * ‖wbar γ v w‖

end SumReLU


