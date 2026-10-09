-- Prove2me | Definitions.Def_ModernOnlineLearning_Aggregating_ExpConcave
-- name    : ModernOnlineLearning_Aggregating_ExpConcave
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:29.027109+00:00
-- url     : https://prove2.me/theorems/583f0b91-a0d5-4fb7-acab-138a2f48e0e2
-- title:
--   Definition 7.31, p. 123 — finite and extended-real exp-concavity
-- statement:
--   A loss $f:\mathbb R^d\to(-\infty,+\infty]$ is **$\alpha$-exp-concave** on a convex set $V\subseteq\mathbb R^d$ when $x\mapsto e^{-\alpha f(x)}$ is concave on $V$, where $\alpha>0$ and $e^{-\alpha(+\infty)}=0$. The same definition is provided for real-valued losses, which are the case used in Theorem 11.5.
--
--   $$e^{-\alpha f(\theta x+(1-\theta)y)}\geq\theta e^{-\alpha f(x)}+(1-\theta)e^{-\alpha f(y)}\quad(x,y\in V,\ 0\leq\theta\leq1).$$
--
--   Convexity of an extended-valued loss is represented by convexity of its epigraph over $V$, the notion used in Proposition 7.34.
--
--   **Formalization Note** WithTop ℝ represents the source's range $(-\infty,+\infty]$. The extended exponential returns zero at $+\infty$.
-- source:
--   Orabona, arXiv:1912.13213v10, Definition 7.31, p. 123; Proposition 7.34, p. 124

import Mathlib
set_option autoImplicit false

namespace ModernOnlineLearning.Aggregating

/-- Definition 7.31 on real-valued losses: the exponential transform is concave on `V`. -/
def ExpConcaveOn {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d)))
    (α : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ConcaveOn ℝ V (fun x => Real.exp (-α * f x))

/-- The book's convention `exp(-α · (+∞)) = 0` for an extended-real loss. -/
noncomputable def extendedExp {d : ℕ} (α : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → WithTop ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ := by
  classical
  exact if f x = ⊤ then 0 else Real.exp (-α * (f x).untopD 0)

/-- Definition 7.31, including the book's `+∞` value. -/
def ExpConcaveOnExtended {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d)))
    (α : ℝ) (f : EuclideanSpace ℝ (Fin d) → WithTop ℝ) : Prop :=
  ConcaveOn ℝ V (extendedExp α f)

/-- Convexity of an extended-real loss, represented by convexity of its epigraph. -/
def ExtendedConvexOn {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → WithTop ℝ) : Prop :=
  Convex ℝ {p : EuclideanSpace ℝ (Fin d) × ℝ | p.1 ∈ V ∧ f p.1 ≤ (p.2 : WithTop ℝ)}

end ModernOnlineLearning.Aggregating


