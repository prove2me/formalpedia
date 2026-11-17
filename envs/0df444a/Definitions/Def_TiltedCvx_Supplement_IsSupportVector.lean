-- Prove2me | Definitions.Def_TiltedCvx_Supplement_IsSupportVector
-- name    : TiltedCvx_Supplement_IsSupportVector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:24:58.059825+00:00
-- url     : https://prove2.me/theorems/ea17d081-fe4f-4c4d-8aea-95037b2d299e
-- title:
--   Support vector at a point (§7, (33))
-- statement:
--   Let $K\subseteq\mathbb R^d$, $f:K\to\mathbb R$, $x\in K$ and $\gamma\in(0,1]$. A vector $q$ is a **support vector** of $f$ at $x$ if the tilted support inequality (4) holds at $x$ with $v=q$ against every point of $K$:
--
--   $$
--   f(y)-f(x)\ \ge\ \psi_\gamma(\langle y-x,q\rangle)\qquad\text{for all }y\in K .
--   $$
--
--   The value-and-support oracle of Section 7 returns such a vector $q_f(x)$; every Clarke subgradient of a $\gamma$–tilted convex function is one.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, §7, (33), p.37

import Mathlib
import Definitions.Def_TiltedCvx_psi

open scoped InnerProductSpace

namespace TiltedCvx.Supplement

/-- **Support vector (§7, (33)).** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, §7, p.37:
for `f : K → ℝ` and `x ∈ K`, a vector `q` is a support vector at `x` if inequality (4) holds at
`x` with `v = q` for every `y ∈ K`, i.e. `f(y) − f(x) ≥ ψγ(⟨y − x, q⟩)` for all `y ∈ K`.

**Formalization Note** `f : E → ℝ`; only its values on `K` enter. -/
def IsSupportVector {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (K : Set E) (f : E → ℝ) (x q : E) : Prop :=
  ∀ y ∈ K, TiltedCvx.psi γ ((⟪y - x, q⟫_ℝ : ℝ) : EReal) ≤ ((f y - f x : ℝ) : EReal)

end TiltedCvx.Supplement


