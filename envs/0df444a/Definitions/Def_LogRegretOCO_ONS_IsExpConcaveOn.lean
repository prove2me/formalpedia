-- Prove2me | Definitions.Def_LogRegretOCO_ONS_IsExpConcaveOn
-- name    : LogRegretOCO_ONS_IsExpConcaveOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:56:57.272264+00:00
-- url     : https://prove2.me/theorems/58db57f8-8e22-400a-b5f0-95134640760d
-- title:
--   $\alpha$-exp-concavity on a set
-- statement:
--   Let $\mathcal P \subseteq \mathbb R^n$, $\alpha \in \mathbb R$ and $f : \mathbb R^n \to \mathbb R$. The function $f$ is **$\alpha$-exp-concave on $\mathcal P$** if
--   $$
--   x \mapsto \exp(-\alpha f(x)) \quad \text{is concave on } \mathcal P .
--   $$
--   The paper (p. 173) calls a sequence of cost functions $\alpha$-exp-concave if there is an $\alpha > 0$ such that each $\exp(-\alpha f_t)$ is concave on $\mathcal P$. For $\alpha > 0$ this class contains every function with bounded gradient and strongly convex Hessian, and the log-loss $-\log(x^\top a)$ of portfolio management. It is the curvature assumption under which Online Newton Step attains logarithmic regret.
--
--   **Formalization Note** Concavity is Mathlib's `ConcaveOn ℝ P`, which includes convexity of $\mathcal P$. The paper's equivalent Hessian form $\nabla^2[\exp(-\alpha f)] \preceq 0$ for twice differentiable $f$ implies this predicate on a convex set. The condition $\alpha > 0$ is a separate hypothesis of the theorems.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Machine Learning 69 (2007) 169–192, doi:10.1007/s10994-007-5016-8, §2.2, p. 173 (PDF p. 5), definition of α-exp-concavity

import Mathlib

namespace LogRegretOCO.ONS

/-- **α-exp-concavity on a set.**
Hazan, Agarwal, Kale, *Logarithmic regret algorithms for online convex optimization*,
Machine Learning 69 (2007) 169–192, §2.2, p. 173: "there is an α > 0 such that exp(−αf_t(x)) is a concave function of
x ∈ P, for all t".

`IsExpConcaveOn α P f` says that `x ↦ exp(−α f(x))` is concave on `P`.

**Formalization Note.** Concavity is Mathlib's `ConcaveOn ℝ P`, which also requires `P` to be
convex. The paper adds "i.e. ∇²[exp(−αf_t(x))] ⪯ 0" for its twice differentiable losses; on a
convex set that Hessian condition implies `ConcaveOn`, so the predicate here is the paper's
concavity condition itself, without differentiability. The paper's `α > 0` is a separate
hypothesis wherever the predicate is used. -/
def IsExpConcaveOn {n : ℕ} (α : ℝ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ConcaveOn ℝ P (fun x => Real.exp (-(α * f x)))

end LogRegretOCO.ONS


