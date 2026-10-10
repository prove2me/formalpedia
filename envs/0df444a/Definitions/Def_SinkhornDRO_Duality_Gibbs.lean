-- Prove2me | Definitions.Def_SinkhornDRO_Duality_Gibbs
-- name    : SinkhornDRO_Duality_Gibbs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:22:53.886529+00:00
-- url     : https://prove2.me/theorems/4c9fc837-7b6e-432e-b3fc-1fcad0b1655c
-- title:
--   The entropy-regularized value $v(\tau)$ of (EC.3) and the function $v_x(\lambda)$ of (8)
-- statement:
--   Let $\nu$ be a measure on a measurable space $\mathcal Z$, let $g:\mathcal Z\to[-\infty,\infty]$ and $\tau\in\mathbb R$. The value (EC.3) is
--
--   $$
--   v(\tau)=\sup_{\mathbb P\in\mathcal P(\mathcal Z),\ \mathbb P\ll\nu}\ \mathbb E_{z\sim\mathbb P}\Big[g(z)-\tau\log\frac{d\mathbb P(z)}{d\nu(z)}\Big].
--   $$
--
--   For a cost $c$, a parameter $\epsilon$, a loss $f$, $\lambda\ge0$ and $x\in\mathcal Z$, the function (8) of the weak-duality proof is the value (EC.3) for $g=f-\lambda c(x,\cdot)$ and $\tau=\lambda\epsilon$:
--
--   $$
--   v_x(\lambda)=\sup_{\gamma_x\in\mathcal P(\mathcal Z)}\ \mathbb E_{z\sim\gamma_x}\Big[f(z)-\lambda c(x,z)-\lambda\epsilon\log\frac{d\gamma_x(z)}{d\nu(z)}\Big].
--   $$
--
--   These values are the inner problems of the Lagrangian relaxation of (Primal); Lemma EC.2 computes them in closed form.
--
--   **Formalization Note** The supremum ranges over probability measures absolutely continuous with respect to $\nu$ (for any other $\mathbb P$ the log-density is undefined), in the extended reals. The density is the Radon–Nikodym derivative and the logarithm is `ENNReal.log`. Expectations are the published extended expectation `DupacovaWets.Consistency.expect` ($\int g^+-\int g^-$ of lower Lebesgue integrals, $+\infty$ when $\int g^+=\infty$). At $\tau=0$ the term $\tau\log(\cdot)$ is $0$, including where the density is $0$ or $\infty$. $v_x(\lambda)$ is defined for every $x$, not only on $\operatorname{supp}\widehat{\mathbb P}$.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. ec13, Lemma EC.2 (EC.3) and Lemma EC.3; p. 12, (8)

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect

open MeasureTheory
open scoped ENNReal
open DupacovaWets.Consistency (expect)

namespace SinkhornDRO.Duality

variable {Z : Type*} [MeasurableSpace Z]

/-- The value (EC.3) of the entropy-regularized problem of Lemma EC.2, arXiv:2109.11926v5,
p. ec13: `v(τ) = sup_{P ∈ P(Z), P ≪ ν} E_{z∼P}[g(z) − τ log (dP/dν)(z)]`, in `EReal`. -/
noncomputable def gibbsValue (ν : Measure Z) (g : Z → EReal) (τ : ℝ) : EReal :=
  ⨆ P ∈ {P : Measure Z | IsProbabilityMeasure P ∧ P ≪ ν},
    expect P (fun z => g z - (τ : EReal) * ENNReal.log (P.rnDeriv ν z))

/-- The function (8) / Lemma EC.3, arXiv:2109.11926v5, p. 12 and p. ec13:
`v_x(λ) = sup_{γ_x ∈ P(Z)} E_{z∼γ_x}[f(z) − λc(x,z) − λε log (dγ_x/dν)(z)]`, i.e. the value (EC.3)
for the function `f − λc(x,·)` and `τ = λε`. -/
noncomputable def vx (ν : Measure Z) (c : Z → Z → ℝ≥0∞) (ε : ℝ) (f : Z → EReal) (lam : ℝ) (x : Z) :
    EReal :=
  gibbsValue ν (fun z => f z - (lam : EReal) * (c x z : EReal)) (lam * ε)

end SinkhornDRO.Duality


