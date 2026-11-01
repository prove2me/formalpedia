-- Prove2me | Definitions.Def_PWDB_PartialConj
-- name    : PWDB_PartialConj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:15.16137+00:00
-- url     : https://prove2.me/theorems/b2a319b4-292c-4ee8-ac42-1d1954c6bebb
-- title:
--   Partial conjugates $f^{*1}$ and $f^{*2}$
-- statement:
--   For $f : E \times F \to \overline{\mathbb R}$ on real inner product spaces,
--   $$
--   f^{*1}(w, z) = \sup_{x \in E}\{\langle w, x\rangle - f(x,z)\}, \qquad f^{*2}(x, y) = \sup_{z \in F}\{\langle y, z\rangle - f(x,z)\}.
--   $$
--   The paper's $(-f)^{*2}(x,y) = \sup_z \{\langle y, z\rangle + f(x,z)\}$ is `pconj2 (fun x z => -f x z)`.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Definition A.3, p.40

import Mathlib

open scoped InnerProductSpace

namespace PWDB

/-- **Partial conjugate with respect to the first argument** (Zhen, Kuhn & Wiesemann,
arXiv:2105.00760v2, Definition A.3, p.40): "The partial conjugate of a function
`f : ℝ^{dx} × ℝ^{dz} → R̄` with respect to its first argument is the function
`f∗1 : ℝ^{dx} × ℝ^{dz} → R̄` defined through `f∗1(w, z) = sup_{x∈ℝ^{dx}} {w⊤x − f(x, z)}`."

**Formalization Note** `f` is curried, `f x z`; the supremum is taken in `EReal`. The spaces are
real inner product spaces `E`, `F`. -/
noncomputable def pconj1 {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → F → EReal) (w : E) (z : F) : EReal :=
  ⨆ x : E, ((⟪w, x⟫_ℝ : ℝ) : EReal) - f x z

/-- **Partial conjugate with respect to the second argument** (arXiv:2105.00760v2, Definition A.3,
p.40): "the partial conjugate of `f` with respect to its second argument is the function
`f∗2 : ℝ^{dx} × ℝ^{dz} → R̄` defined through `f∗2(x, y) = sup_{z∈ℝ^{dz}} {y⊤z − f(x, z)}`."
The paper's `(−f)∗2` is `pconj2 (fun x z => -f x z)`. -/
noncomputable def pconj2 {E F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E → F → EReal) (x : E) (y : F) : EReal :=
  ⨆ z : F, ((⟪y, z⟫_ℝ : ℝ) : EReal) - f x z

end PWDB


