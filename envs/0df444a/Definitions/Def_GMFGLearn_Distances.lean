-- Prove2me | Definitions.Def_GMFGLearn_Distances
-- name    : GMFGLearn_Distances
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:52:22.14143+00:00
-- url     : https://prove2.me/theorems/7cf72ceb-8b69-4888-ab56-2d87e707f330
-- title:
--   The Wasserstein distance $W_1$, the $\ell_2$ product cost on $\mathcal S\times\mathcal A$, $\operatorname{diam}(\mathcal S\times\mathcal A)$ and $d_{TV}$
-- statement:
--   Let $(X,d_X)$ be a metric space with its Borel $\sigma$-field and let $\mathcal P(X)$ be the set of Borel probability measures on $X$. For a cost $c:X\times X\to\mathbb R$, the **1-Wasserstein distance** between $\mu,\mu'\in\mathcal P(X)$ is
--
--   $$
--   W_1(\mu,\mu')=\inf\Big\{\int_{X\times X}c(x,x')\,\nu(dx,dx') : \nu\in\mathcal P(X\times X)\text{ with marginals }\mu,\mu'\Big\}.
--   $$
--
--   The paper takes $c=d_X$. On the product $\mathcal S\times\mathcal A$ of the state and action spaces it uses the Euclidean distance of $\mathcal S\times\mathcal A\subseteq\mathbb R^{d+p}$, the **$\ell_2$ product cost**
--
--   $$
--   d_{\mathcal S\times\mathcal A}\big((s,a),(s',a')\big)=\sqrt{d_{\mathcal S}(s,s')^2+d_{\mathcal A}(a,a')^2},
--   $$
--
--   and $\operatorname{diam}(\mathcal S\times\mathcal A)=\sup_{x,y}d_{\mathcal S\times\mathcal A}(x,y)$. On a finite set $X$, the **total variation distance** is $d_{TV}(\nu,\nu')=\tfrac12\sum_{x\in X}|\nu\{x\}-\nu'\{x\}|=\tfrac12\|\nu-\nu'\|_1$.
--
--   $W_1$ is the metric on population state-action distributions throughout the mission; $d_{TV}$ measures the $\epsilon$-net and the projection of the learning algorithm.
--
--   **Formalization Note** $\mathcal P(X)$ is `ProbabilityMeasure X`. $W_1$ is a real infimum; the product coupling always lies in the set and a nonnegative cost bounds it below by $0$, so the infimum is genuine. Lean's default product metric is the max metric, so the $\ell_2$ cost is written out.
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, Notations, p.3; (52), p.36; (39), p.21; Appendix A, p.36 (diam)

import Mathlib

open MeasureTheory

namespace GMFGLearn

/-- **The 1-Wasserstein distance with cost `cost`.** Guo–Hu–Xu–Zhang, *A General Framework for
Learning Mean-Field Games*, arXiv:2003.06069v3, Notations, p.3, and (52), p.36:
`W_p(µ,µ′) = inf{∫_{X×X} d^p_X(x,x′) ν(dx,dx′) : ν ∈ P(X × X) with marginals µ,µ′ ∈ P(X)}`, here
with `p = 1`.

**Formalization Note** `P(X)` is `MeasureTheory.ProbabilityMeasure X`. The infimum is the real
`sInf` over the set of transport costs `∫ cost(x,x′) dγ` of all couplings `γ` of `µ` and `ν`. The
product coupling `µ ⊗ ν` always belongs to this set, and for a nonnegative cost the set is bounded
below by `0`, so `sInf` is a genuine infimum. The cost is explicit so that the same definition
serves `dist` on `S`, on `A`, and the ℓ₂ product cost `dSA` on `S × A`. For a continuous cost on a
compact metric space with its Borel σ-algebra the integrand is bounded and measurable, so every
integral in the set is a genuine (finite) integral. -/
noncomputable def W1 {X : Type*} [MeasurableSpace X] (cost : X → X → ℝ)
    (μ ν : ProbabilityMeasure X) : ℝ :=
  sInf {t : ℝ | ∃ γ : ProbabilityMeasure (X × X),
    (γ : Measure (X × X)).map Prod.fst = (μ : Measure X) ∧
    (γ : Measure (X × X)).map Prod.snd = (ν : Measure X) ∧
    t = ∫ z, cost z.1 z.2 ∂(γ : Measure (X × X))}

/-- **The ℓ₂ product cost on `S × A`.** Guo–Hu–Xu–Zhang, arXiv:2003.06069v3, §2.1, p.3
(`S ⊆ ℝ^d`, `A ⊆ ℝ^p`) and (52), p.36 (`W₁` on `X ⊆ ℝ^k` uses `‖x − y‖₂`): for `S × A ⊆ ℝ^{d+p}`
the Euclidean distance is `√(d_S(s,s′)² + d_A(a,a′)²)`.

**Formalization Note** Lean's default metric on a product is the max metric, which is not the
paper's; this explicit cost is used instead. -/
noncomputable def dSA {S A : Type*} [PseudoMetricSpace S] [PseudoMetricSpace A]
    (x y : S × A) : ℝ :=
  Real.sqrt (dist x.1 y.1 ^ 2 + dist x.2 y.2 ^ 2)

/-- **The diameter of `S × A`** in the ℓ₂ product cost: `diam(S × A) = sup_{x,y ∈ S×A} ‖x − y‖₂`.
Guo–Hu–Xu–Zhang, arXiv:2003.06069v3, Appendix A, p.36 (`diam(X) = sup_{x,y∈X} ‖x − y‖₂`).

**Formalization Note** A real `⨆` over pairs; for compact (in particular finite) `S`, `A` the
range is bounded, so it is a genuine supremum. -/
noncomputable def diamSA (S A : Type*) [PseudoMetricSpace S] [PseudoMetricSpace A] : ℝ :=
  ⨆ p : (S × A) × (S × A), dSA p.1 p.2

/-- **Total variation distance on a finite set.** Guo–Hu–Xu–Zhang, arXiv:2003.06069v3, (39),
p.21: `d_TV(ν,ν′) = ½‖ν − ν′‖₁`, where `ν`, `ν′` are viewed as vectors of length `|X|`.

**Formalization Note** `ν{x}` is `(ν : Measure X).real {x}`. -/
noncomputable def dTV {X : Type*} [Fintype X] [MeasurableSpace X]
    (μ ν : ProbabilityMeasure X) : ℝ :=
  (1 / 2) * ∑ x, |(μ : Measure X).real {x} - (ν : Measure X).real {x}|

end GMFGLearn


