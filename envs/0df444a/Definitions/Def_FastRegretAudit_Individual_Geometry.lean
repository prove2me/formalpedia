-- Prove2me | Definitions.Def_FastRegretAudit_Individual_Geometry
-- name    : FastRegretAudit_Individual_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:33:18.393869+00:00
-- url     : https://prove2.me/theorems/0af8501d-f9f2-4533-be4f-6e00887b8552
-- title:
--   Arbitrary primal and dual norms; minimal midpoint strong convexity
-- statement:
--   Let $d\ge1$ and let $\Delta=\{a\in\mathbb R^d:a_x\ge0,\ \sum_xa_x=1\}$. A primal norm $p$ is a Mathlib seminorm separating points. Its coordinate dual is
--
--   $$p_*(z)=\sup_{p(v)\le1}\langle v,z\rangle.$$
--
--   For a real-valued regularizer $\mathcal R$, the midpoint strong-convexity condition is exactly
--
--   $$\mathcal R((a+b)/2)\le\frac{\mathcal R(a)+\mathcal R(b)}2-\frac{p(a-b)^2}{8}\qquad(a,b\in\Delta).$$
--
--   The predicate also accepts the explicit $\ell_1$ norm for the game theorem. No continuity, differentiability, interiority, or full-segment convexity is included. The norm and its dual are shared by all single-player bounds; the finite-dimensional genuine-norm unit ball makes the real dual supremum well-defined.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, main p. 3, footnote 1; main p. 4, footnote 3, PDF pp. 3–4

import Mathlib

namespace FastRegretAudit.Individual

/-- A genuine arbitrary norm on the coordinate space, using Mathlib's seminorm
interface with separation of points. No topology on the regularizer is imposed. -/
abbrev PrimalNorm (d : ℕ) :=
  {p : Seminorm ℝ (Fin d → ℝ) // ∀ v, p v = 0 → v = 0}

/-- Footnote 1, main p. 3: the dual norm for the coordinate pairing.
The unit ball is nonempty and bounded for every genuine norm in finite dimension. -/
noncomputable def dualNorm {d : ℕ} (p : PrimalNorm d) (z : Fin d → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ v : Fin d → ℝ, p.val v ≤ 1 ∧ r = v ⬝ᵥ z}

/-- Exactly footnote 3, main p. 4, on the feasible simplex. In particular this
predicate does not include continuity or full-segment convexity. -/
def IsMidpointStronglyConvex {d : ℕ}
    (N : (Fin d → ℝ) → ℝ) (𝓡 : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ a ∈ stdSimplex ℝ (Fin d), ∀ b ∈ stdSimplex ℝ (Fin d),
    𝓡 ((1 / 2 : ℝ) • (a + b)) ≤ (𝓡 a + 𝓡 b) / 2 - (N (a - b)) ^ 2 / 8

end FastRegretAudit.Individual


