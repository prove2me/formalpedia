-- Prove2me | Definitions.Def_FTPLLinBandit_IsArgmaxSel
-- name    : FTPLLinBandit_IsArgmaxSel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:13.148751+00:00
-- url     : https://prove2.me/theorems/c855b7ad-8801-4a79-baa7-6427d4fb65bb
-- title:
--   Linear optimization oracle: a measurable selection $x(\Theta)\in\arg\max_{a\in A}\langle a,\Theta\rangle$
-- statement:
--   Let $A\subseteq\mathbb R^d$. A map $x:\mathbb R^d\to\mathbb R^d$ is an **argmax selection** of $A$ when, for every $\Theta\in\mathbb R^d$,
--   $$x(\Theta)\in A\qquad\text{and}\qquad \langle a,\Theta\rangle\le\langle x(\Theta),\Theta\rangle\ \text{ for all } a\in A,$$
--   and $x$ is Borel measurable.
--
--   This is the paper's linear optimization oracle with "a fixed tie-breaking rule" (Algorithm 1, line 16), written $x(\Theta)=\arg\max_{a\in A}\langle a,\Theta\rangle$ in Section 5, "where we break ties in $x(\Theta)$ in an arbitrary but fixed way". The FTPL action is $x(\hat\Theta_t+Z_t)$ for a random perturbation $Z_t$.
--
--   **Formalization Note** Measurability is the convention under which $x(\Theta+Z)$ is a random variable, as the paper's expectations require. Every fixed tie-breaking rule is an argmax selection; for a compact $A$ a measurable selection exists, so the hypothesis is satisfiable.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, §2, p.4; Algorithm 1 line 16, p.8; §5, p.9

import Mathlib

open scoped InnerProductSpace

namespace FTPLLinBandit

/-- **The linear optimization oracle `x(Θ) ∈ argmax_{a∈A} ⟨a, Θ⟩` with a fixed tie-breaking
rule.** Wei, arXiv:2610.17818, §2, p.4 ("The learner has an action set A ⊂ ℝ^d and access to a
linear optimization oracle over A"); Algorithm 1, line 16, p.8 ("return an action in
arg max_{a∈A}⟨a, Θ + Z⟩, using a fixed tie-breaking rule"); §5, p.9 ("x(Θ) = arg max_{a∈A}⟨a, Θ⟩,
where we break ties in x(Θ) in an arbitrary but fixed way").

`IsArgmaxSel A x` says that the fixed map `x : ℝ^d → ℝ^d` returns, for every `Θ`, a point of `A`
maximizing `a ↦ ⟨a, Θ⟩` over `A`, and that `x` is (Borel) measurable.

**Formalization Note.** Any measurable selection of the argmax is allowed; a fixed tie-breaking
rule is one such selection. Measurability is the convention that makes `x(Θ + Z)` a random
variable, which the paper uses implicitly when it takes expectations of it. For a compact `A` a
measurable selection exists (measurable selection theorem), so the hypothesis is satisfiable. -/
def IsArgmaxSel {d : ℕ} (A : Set (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  Measurable x ∧ ∀ Θ, x Θ ∈ A ∧ ∀ a ∈ A, ⟪a, Θ⟫_ℝ ≤ ⟪x Θ, Θ⟫_ℝ

end FTPLLinBandit


