-- Prove2me | Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
-- name    : EntropicBarrier_Universal_EntropicBarrier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:42:15.517372+00:00
-- url     : https://prove2.me/theorems/c90ca4e7-3e33-4e20-a1d0-316e92a808f8
-- title:
--   Convex body, log-Laplace transform $f(\theta)=\log\int_{\mathcal K} e^{\langle\theta,x\rangle}dx$ and its Fenchel dual $f^*$ (the entropic barrier)
-- statement:
--   Work in $\mathbb R^n$ with its Euclidean inner product $\langle\cdot,\cdot\rangle$ and Lebesgue measure $dx$.
--
--   1. A **convex body** is a set $\mathcal K\subset\mathbb R^n$ that is compact, convex and has non-empty interior $\operatorname{int}(\mathcal K)$.
--   2. The **log-Laplace transform** of the uniform measure on $\mathcal K$ is the function $f:\mathbb R^n\to\mathbb R$,
--   $$f(\theta)=\log\left(\int_{x\in\mathcal K}\exp(\langle\theta,x\rangle)\,dx\right).$$
--   3. The **entropic barrier** of $\mathcal K$ is the Fenchel dual of $f$,
--   $$f^*(x)=\sup_{\theta\in\mathbb R^n}\ \langle\theta,x\rangle-f(\theta),\qquad x\in\operatorname{int}(\mathcal K).$$
--
--   These are the objects of Theorem 1 of Bubeck and Eldan: $f$ is the log-partition function of the canonical exponential family of $\mathcal K$, and $f^*$ is the barrier whose self-concordance parameter the paper bounds by $(1+o(1))n$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, so $n$ is the dimension itself. For a convex body the integral in $f$ is finite and strictly positive (a continuous positive integrand on a compact set of positive volume), so the logarithm is the true one. $f^*$ is a real supremum (`⨆`); for $x\in\operatorname{int}(\mathcal K)$ the family $\theta\mapsto\langle\theta,x\rangle-f(\theta)$ is bounded above, so the value is the true supremum. Outside $\operatorname{int}(\mathcal K)$ the family is unbounded and Lean's `⨆` returns the junk value $0$; no statement of this mission evaluates $f^*$ there (all clauses quantify over $\operatorname{int}(\mathcal K)$ or take limits within it). The definition of a convex body asks for a non-empty interior, which rules out lower-dimensional sets.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 1, §1 and Theorem 1, eq. (1)

import Mathlib

open scoped RealInnerProductSpace

namespace EntropicBarrier.Universal

/-- A **convex body** in `ℝⁿ` (p. 1): a compact convex set with non-empty interior. -/
def IsConvexBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- The **log-Laplace transform** of the uniform (Lebesgue) measure on `K`, eq. (1):
`f(θ) = log ∫_{x ∈ K} exp ⟪θ, x⟫ dx`. -/
noncomputable def logPartition {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.log (∫ x in K, Real.exp ⟪θ, x⟫)

/-- The **entropic barrier** (Theorem 1): the Fenchel dual
`f*(x) = sup_{θ ∈ ℝⁿ} ⟪θ, x⟫ - f(θ)` of the log-Laplace transform, as a real supremum.
Only its values on `interior K` are meaningful (there the family is bounded above). -/
noncomputable def entropicBarrier {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨆ θ : EuclideanSpace ℝ (Fin n), (⟪θ, x⟫ - logPartition K θ)

end EntropicBarrier.Universal


