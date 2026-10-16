-- Prove2me | Definitions.Def_ZORiem_RSGD_zoGradBatch
-- name    : ZORiem_RSGD_zoGradBatch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:52.504657+00:00
-- url     : https://prove2.me/theorems/0b9c2711-6833-47f2-86f9-67621ccc348f
-- title:
--   (3.6) and Algorithm 2 step 3, pp. 16–17 — the mini-batch zeroth-order Riemannian stochastic gradient and the law of one batch
-- statement:
--   Let $(\Xi, P_\xi)$ be a probability space of noise and $F : E \times \Xi \to \mathbb R$ a stochastic objective. Given $m \in \mathbb N$ pairs $(u_{0,i}, \xi_i)$, $i = 1, \dots, m$, put $u_i = P u_{0,i}$ (projection onto $T_x\mathcal M$). The **mini-batch zeroth-order Riemannian stochastic gradient** is
--
--   $$\bar g_{\mu,\xi}(x) = \frac1m\sum_{i=1}^m g_{\mu,\xi_i}(x), \qquad g_{\mu,\xi_i}(x) = \frac{F(R_x(\mu u_i), \xi_i) - F(x, \xi_i)}{\mu}\,u_i .$$
--
--   Both evaluations of $F$ in the $i$-th term use the same sample $\xi_i$.
--
--   The **law of one batch** is the product measure on $(E \times \Xi)^m$ under which the $m$ pairs are independent and identically distributed, and in each pair $u_{0,i} \sim \mathcal N(0, I)$ (the standard Gaussian on $E$) is independent of $\xi_i \sim P_\xi$; this is step 3 of Algorithm 2.
--
--   **Formalization Note** `zoGradBatch M R F mu m x s` takes the batch $s : \{0,\dots,m-1\} \to E \times \Xi$ and is $\frac1m\sum_i$ of `zoGrad` applied to the function $F(\cdot, \xi_i)$ and the draw $u_{0,i}$. `batchLaw E Pξ m` is `Measure.pi` of `(stdGaussian E).prod Pξ`; an instance records that it is a probability measure. For $m = 0$ the factor $1/m$ is $0$ in Lean; every statement of the mission assumes $m \ge 1$.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, (3.6), p. 16; Algorithm 2, step 3, p. 17

import Mathlib
import Definitions.Def_ZORiem_RGD_zoGrad

namespace ZORiem.RSGD

open MeasureTheory ProbabilityTheory

/-- (3.6), p. 16: the mini-batch zeroth-order Riemannian stochastic gradient
`ḡ_{µ,ξ}(x) = (1/m) Σ_{i=1}^m g_{µ,ξ_i}(x)`, with
`g_{µ,ξ_i}(x) = ((F(R_x(µ u_i), ξ_i) − F(x, ξ_i)) / µ) u_i` and `u_i = P u₀ᵢ`. The batch
`s : Fin m → E × Ξ` holds the pairs `(u₀ᵢ, ξᵢ)`; both evaluations of `F` in the `i`-th term use the
same `ξᵢ`. -/
noncomputable def zoGradBatch {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {Ξ : Type*} (M : Set E) (R : E → E → E) (F : E → Ξ → ℝ) (mu : ℝ)
    (m : ℕ) (x : E) (s : Fin m → E × Ξ) : E :=
  (1 / (m : ℝ)) • ∑ i, ZORiem.RGD.zoGrad M R (fun y => F y (s i).2) mu x (s i).1

/-- Algorithm 2, step 3, p. 17: the law of one batch, `m` independent pairs `(u₀ᵢ, ξᵢ)`, each with
`u₀ᵢ ∼ N(0, I)` on `E` independent of `ξᵢ ∼ P`. -/
noncomputable def batchLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {Ξ : Type*} [MeasurableSpace Ξ]
    (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ] (m : ℕ) : Measure (Fin m → E × Ξ) :=
  Measure.pi (fun _ => (stdGaussian E).prod Pξ)

instance batchLaw.instIsProbabilityMeasure (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ξ : Type*} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ] (m : ℕ) :
    IsProbabilityMeasure (batchLaw E Pξ m) := by
  unfold batchLaw; infer_instance

end ZORiem.RSGD


