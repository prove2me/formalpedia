-- Prove2me | Definitions.Def_DualRCD_IsPolyhedral
-- name    : DualRCD_IsPolyhedral
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:35.499748+00:00
-- url     : https://prove2.me/theorems/6be5ff7e-cc09-4baf-9d21-1d5eef66a988
-- title:
--   Polyhedral subset of $\mathbb R^n$
-- statement:
--   A set $P\subseteq\mathbb R^n$ is polyhedral if it is the solution set of finitely many linear inequalities: there are $a_1,\dots,a_p\in\mathbb R^n$ and $b_1,\dots,b_p\in\mathbb R$ with
--   $$
--   P=\{x:\langle a_j,x\rangle\le b_j,\ j=1,\dots,p\}.
--   $$
--   Polyhedral sets get the relaxed treatment in Slater's condition: a feasible point need not lie in their relative interior.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, Definition 2, p.5

import Mathlib

open scoped RealInnerProductSpace

namespace DualRCD

/-- A polyhedral subset of `ℝⁿ`: the solution set of finitely many linear inequalities
`⟨aⱼ, x⟩ ≤ bⱼ` (used in Slater's condition, Definition 2, Necoara & Fercoq, arXiv:1911.06014v1, p.5).

**Formalization Note.** An equality is a pair of inequalities, and `p = 0` gives the whole space. -/
def IsPolyhedral {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (p : ℕ) (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ),
    P = {x | ∀ j, ⟪a j, x⟫ ≤ b j}

end DualRCD


