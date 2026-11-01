-- Prove2me | Definitions.Def_PWDB_IsAffineFn
-- name    : PWDB_IsAffineFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:11.914259+00:00
-- url     : https://prove2.me/theorems/d9afbd0f-7722-491b-9365-f707df857ebb
-- title:
--   Affine extended-real function
-- statement:
--   A function $g : X \to \overline{\mathbb R}$ on a real vector space is **affine** if there are a linear functional $\varphi$ and a constant $b \in \mathbb R$ with $g(x) = \varphi(x) + b$ for all $x$.
--
--   Condition (iii) of Definition 1 (Slater points) exempts such constraint functions from strict satisfaction: "nonlinear" is read as "not affine", as in the paper's Definition A.6 (p.41).
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Definition 1, p.6 and Definition A.6, p.41

import Mathlib

namespace PWDB

/-- **Affine function**, the exemption in condition (iii) of Definition 1 (Zhen, Kuhn &
Wiesemann, arXiv:2105.00760v2, Definition 1, p.6: "`fi(xS) < 0` for all `i ∈ I` such that `fi` is
nonlinear"; Definition A.6, p.41: "with the exception of those for which `fi` is affine").

`IsAffineFn g` says that `g` is real-valued and of the form `x ↦ φ(x) + b` for a linear functional
`φ` and a constant `b`.

**Formalization Note** "Nonlinear" in Definition 1 is read as "not affine", the reading the paper
itself spells out in its conic version, Definition A.6 (p.41). -/
def IsAffineFn {X : Type*} [AddCommGroup X] [Module ℝ X] (g : X → EReal) : Prop :=
  ∃ (φ : X →ₗ[ℝ] ℝ) (b : ℝ), ∀ x, g x = ((φ x + b : ℝ) : EReal)

end PWDB


