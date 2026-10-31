-- Prove2me | Definitions.Def_DualRCD_suppFn
-- name    : DualRCD_suppFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:39.404472+00:00
-- url     : https://prove2.me/theorems/aedcd521-db6b-4543-9019-788c557ef2ba
-- title:
--   Support function $\mathrm{supp}_X$
-- statement:
--   The support function of a set $X\subseteq\mathbb R^n$ is
--   $$
--   \operatorname{supp}_X(y)=\sup_{x\in X}\langle y,x\rangle ,
--   $$
--   which the paper writes as a maximum. It is the Fenchel conjugate of the indicator function of $X$, and it appears in the dual problem as the nonsmooth part.
--
--   **Formalization Note.** The value is in the extended reals, since it is $+\infty$ when $\langle y,\cdot\rangle$ is unbounded above on $X$. This is the published support functional at the linear form $\langle y,\cdot\rangle$.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, Notation, p.4

import Mathlib
import Definitions.Def_VectorSpaceOpt_support_functional

namespace DualRCD

/-- The support function `supp_X(y) := max_{x ∈ X} ⟨y, x⟩` (Necoara & Fercoq, arXiv:1911.06014v1,
Notation, p.4), valued in `EReal`.

**Formalization Note.** This is the published `VectorSpaceOpt_support_functional` at the functional
`⟨y, ·⟩`. It is `+∞` when `⟨y, ·⟩` is unbounded above on `X`, which is why the dual function is
`EReal`-valued, and `⊥` for empty `X`, a case that Slater's condition excludes. -/
noncomputable def suppFn {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (y : EuclideanSpace ℝ (Fin n)) : EReal :=
  VectorSpaceOpt_support_functional X (innerSL ℝ y)

end DualRCD


