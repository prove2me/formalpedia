-- Prove2me | Definitions.Def_BoundConstrainedPatternSearch_FullConvergence_LevelSetRegularity
-- name    : BoundConstrainedPatternSearch_FullConvergence_LevelSetRegularity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:39:32.424188+00:00
-- url     : https://prove2.me/theorems/f7544863-20a8-49a3-ad7c-d0f18d4e296a
-- title:
--   Ambient continuous differentiability on the feasible level set
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, let $\Omega=\{x:\ell\le x\le u\}$, and fix $x_0\in\mathbb R^n$. Write $S=L_\Omega(x_0)=\{x\in\Omega:f(x)\le f(x_0)\}$. The regularity predicate means
--
--   $$
--   (\forall x\in S,\ f\text{ is differentiable at }x\text{ in }\mathbb R^n)
--   \quad\text{and}\quad (\nabla f)|_S\text{ is continuous}.
--   $$
--
--   The derivative is the ambient derivative of the given objective, including at boundary points or when $S$ has empty interior. This is the explicit reading of the paper's continuous differentiability on $L_\Omega(x_0)$; no open neighborhood of all $\Omega$, global smoothness, or freely chosen gradient field is required. The predicate shares the published feasible level set and projected-gradient definitions.
-- source:
--   Lewis and Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report 96-20, March 1996, printed p. 7 (PDF p. 9), Theorems 3.2–3.3 and standing setup

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_ProjQ

namespace BoundConstrainedPatternSearch.FullConvergence

/-- The closed-set regularity reading of Theorems 3.2–3.3 (printed p. 7):
ambient differentiability at each feasible sublevel point and continuity of the
actual ambient gradient restricted to that set, including sets with empty interior. -/
def LevelSetRegularity {n : ℕ} (lo hi : Fin n → EReal)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ x ∈ LewisTorczon.BoundPS.levelSet lo hi f x₀, DifferentiableAt ℝ f x) ∧
    ContinuousOn (gradient f) (LewisTorczon.BoundPS.levelSet lo hi f x₀)

end BoundConstrainedPatternSearch.FullConvergence


