-- Prove2me | Definitions.Def_SinkhornDRO_Duality_SinkhornDistance
-- name    : SinkhornDRO_Duality_SinkhornDistance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:22:47.112307+00:00
-- url     : https://prove2.me/theorems/1eaf0e83-cc07-4152-ba74-e7015d822add
-- title:
--   Definition 1 — Sinkhorn distance, and the primal value $V$ of Sinkhorn DRO
-- statement:
--   Let $\mathcal Z$ be a measurable space. For probability measures $\mathbb P,\mathbb Q$ on $\mathcal Z$, let $\Gamma(\mathbb P,\mathbb Q)$ be the set of probability measures $\gamma$ on $\mathcal Z\times\mathcal Z$ whose first and second marginals are $\mathbb P$ and $\mathbb Q$.
--
--   **Sinkhorn distance (Definition 1).** Fix reference measures $\mu,\nu$ on $\mathcal Z$, a transport cost $c:\mathcal Z\times\mathcal Z\to[0,\infty]$ and a regularization parameter $\epsilon\ge0$. The Sinkhorn distance is
--
--   $$
--   \mathcal W_\epsilon(\mathbb P,\mathbb Q)=\inf_{\gamma\in\Gamma(\mathbb P,\mathbb Q)}\ \mathbb E_{(x,y)\sim\gamma}\Big[c(x,y)+\epsilon\log\frac{d\gamma(x,y)}{d\mu(x)\,d\nu(y)}\Big],
--   $$
--
--   i.e. the expected transport cost plus $\epsilon$ times the relative entropy $H(\gamma\mid\mu\otimes\nu)$. For $\epsilon>0$ a coupling that is not absolutely continuous with respect to $\mu\otimes\nu$ has undefined relative entropy and contributes $+\infty$.
--
--   **Primal value.** Given a nominal distribution $\widehat{\mathbb P}$, a radius $\rho\in\mathbb R$ and a loss $f:\mathcal Z\to\mathbb R\cup\{\infty\}$, the worst-case expected loss over the Sinkhorn ball, with reference measures $\mu=\widehat{\mathbb P}$ (Remark 2) and $\nu$, is
--
--   $$
--   V=\sup\Big\{\mathbb E_{z\sim\mathbb P}[f(z)]\ :\ \mathbb P\in\mathcal P(\mathcal Z),\ \mathcal W_\epsilon(\widehat{\mathbb P},\mathbb P)\le\rho\Big\}.\qquad(\text{Primal})
--   $$
--
--   The infeasible problem has $V=-\infty$.
--
--   These are the objects of the strong duality theorem: $V$ is the left-hand side of every duality statement in the mission.
--
--   **Formalization Note** Definition 1's "$\mathbb E_\gamma[c]+\epsilon H(\gamma\mid\mu\otimes\nu)$" is integrated as a single expectation of the combined integrand, as the paper itself writes it in the proofs on pp. 11 and 13; this avoids an undefined sum $\infty+(-\infty)$. Expectations use the published extended expectation `DupacovaWets.Consistency.expect` ($\int g^+-\int g^-$ with $\infty-\infty=+\infty$). The infimum and supremum are taken in the extended reals. The density ratio is Mathlib's Radon–Nikodym derivative and the logarithm is `ENNReal.log`, with $\log 0=-\infty$ and $\log\infty=+\infty$. At $\epsilon=0$ the entropy term is absent and every coupling is admitted.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. 5, Definition 1; p. 6, Remark 2 and (Primal)

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect

open MeasureTheory
open scoped ENNReal
open DupacovaWets.Consistency (expect)

namespace SinkhornDRO.Duality

variable {Z : Type*} [MeasurableSpace Z]

/-- `Γ(P, Q)`: the joint probability distributions on `Z × Z` whose first and second marginals
are `P` and `Q`. -/
def couplings (P Q : Measure Z) : Set (Measure (Z × Z)) :=
  {γ | IsProbabilityMeasure γ ∧ γ.map Prod.fst = P ∧ γ.map Prod.snd = Q}

open scoped Classical in
/-- Definition 1 (Sinkhorn distance), arXiv:2109.11926v5, p. 5: for reference measures `μ, ν`,
transport cost `c` and regularization `ε ≥ 0`,
`W_ε(P, Q) = inf_{γ ∈ Γ(P,Q)} E_{(x,y)∼γ}[c(x,y) + ε log (dγ/d(μ⊗ν))(x,y)]`.

The cost and the entropy are integrated as one integrand (as on pp. 11 and 13 of the paper), with
the expectation `expect` (`∞ − ∞ = +∞`). For `ε > 0` a coupling that is not absolutely continuous
with respect to `μ ⊗ ν` has undefined relative entropy and contributes `+∞`; for `ε = 0` the
entropy term vanishes and every coupling is admitted. The infimum is taken in `EReal`, so an
empty set of couplings gives `+∞`. -/
noncomputable def sinkhornDist (μ ν : Measure Z) (c : Z → Z → ℝ≥0∞) (ε : ℝ) (P Q : Measure Z) :
    EReal :=
  ⨅ γ ∈ couplings P Q,
    if ε = 0 ∨ γ ≪ μ.prod ν then
      expect γ (fun p => (c p.1 p.2 : EReal) + (ε : EReal) * ENNReal.log (γ.rnDeriv (μ.prod ν) p))
    else ⊤

/-- (Primal), arXiv:2109.11926v5, p. 6: the worst-case expectation
`V = sup { E_{z∼P}[f(z)] : P ∈ P(Z), W_ε(P̂, P) ≤ ρ }` over the Sinkhorn ball of radius `ρ`
around the nominal distribution `P̂`, with the reference measures `µ = P̂` (Remark 2) and `ν`.
The supremum is in `EReal`; the empty supremum (infeasible primal) is `−∞`. -/
noncomputable def primalValue (Phat ν : Measure Z) (c : Z → Z → ℝ≥0∞) (ε ρ : ℝ) (f : Z → EReal) :
    EReal :=
  ⨆ P ∈ {P : Measure Z | IsProbabilityMeasure P ∧ sinkhornDist Phat ν c ε Phat P ≤ (ρ : EReal)},
    expect P f

end SinkhornDRO.Duality


