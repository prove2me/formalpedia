-- Prove2me | Definitions.Def_TalagrandConc_QPoints_aConst
-- name    : TalagrandConc_QPoints_aConst
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:38:33.280662+00:00
-- url     : https://prove2.me/theorems/931902fb-5d50-4dae-99b7-0bfb8656b7a8
-- title:
--   The constant $a(q,\alpha)$ of (3.2.2)
-- statement:
--   For an integer $q\ge 2$ and a real $\alpha\ge 1$, Talagrand's constant $a(q,\alpha)$ is the unique number $x>1$ with
--   $$x+q\alpha\,x^{-1/\alpha}=1+q\alpha .$$
--   It is defined here as the largest such solution in the form
--   $$a(q,\alpha)=\sup\{\,x>1:\ x+q\alpha\,x^{-1/\alpha}\le 1+q\alpha\,\}.$$
--   Since $x\mapsto x+q\alpha x^{-1/\alpha}$ is strictly convex, equals $1+q\alpha$ at $x=1$, decreases just to the right of $1$ (its derivative there is $1-q<0$) and tends to $+\infty$, the set above is an interval $(1,a]$ and its supremum is the root of the equation; that this root exists and is unique is stated separately as a theorem. For $\alpha=1$ the definition gives $a(q,1)=q$.
--
--   $a(q,\alpha)$ is the base of the exponential moment in the sharpened inequality (3.2.1).
--
--   **Formalization Note** The supremum is Mathlib's real `sSup`; the accompanying theorem (3.2.2) asserts that the set is nonempty and bounded for $q\ge2$, $\alpha>1$, so no junk value is used.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 114, Eq. (3.2.2)

import Mathlib

namespace TalagrandConc.QPoints

/-- Talagrand's `a(q, α)` of (3.2.2): the largest `x > 1` with
`x + q α x^{-1/α} ≤ 1 + q α`. For `q ≥ 2` and `α ≥ 1` this set is `(1, a]`, so `a(q, α)`
is the unique `x > 1` solving `x + q α x^{-1/α} = 1 + q α`. -/
noncomputable def aConst (q : ℕ) (α : ℝ) : ℝ :=
  sSup {x : ℝ | 1 < x ∧ x + (q : ℝ) * α * x ^ (-(1 / α)) ≤ 1 + (q : ℝ) * α}

end TalagrandConc.QPoints


