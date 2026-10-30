-- Prove2me | Definitions.Def_RobustDP_ChiSquareAudit_Model
-- name    : RobustDP_ChiSquareAudit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:42:29.905984+00:00
-- url     : https://prove2.me/theorems/03ba0638-faea-42a9-a678-4a3836875e96
-- title:
--   Support-aware chi-square ball and clipped scalar objective
-- statement:
--   Let $S$ be a finite set and $q:S\to\mathbb R$ a probability vector. The support-aware uncertainty set consists of probability vectors $p$ such that $p(s)=0$ wherever $q(s)=0$ and
--   $$\sum_{s:q(s)>0}\frac{(p(s)-q(s))^2}{q(s)}\le t.$$
--   An equivalent extended nonnegative divergence assigns zero to $0/0$ and infinity to nonzero mass divided by zero. On positive centres the set agrees with the published chi-square set. These functions are defined on raw inputs, but all probability interpretations require normalization and $t\ge0$ in the theorems.
--
--   For real $\alpha$, the clipped multiplier is $\mu_\alpha(s)=\max(v(s)-\alpha,0)$. The scalar objective is the published dual objective at this multiplier. For stored moments $(a,b,c)$ the interval variance is $Q(\alpha)=c+b\alpha^2-(a+b\alpha)^2$ and the score is $a+b\alpha-\sqrt{tQ(\alpha)}$. The corrected stationary polynomial is $b^2Q(\alpha)-tb^2((1-b)\alpha-a)^2$.
--
--   This layer reuses the published expectation, centred variance, simplex and dual objective; it adds no optimization witness or unproved mathematical fact. The zero-support extension and the corrected expressions are explicit conventions documented in the theorem items.
-- source:
--   G. Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07, revised May 4, 2004, p. 18–19, Section 4.2, (46), (48), (53)–(54)

import Mathlib
import Definitions.Def_RobustDP_ChiSquare_Moments
import Definitions.Def_RobustDP_ChiSquare_ChiSqSet

namespace RobustDP.ChiSquareAudit

open RobustDP.ChiSquare

/-- Zero coordinates force zero mass; division is evaluated only on positive support. -/
noncomputable def supportBall {S : Type*} [Fintype S]
    (q : S → ℝ) (t : ℝ) : Set (S → ℝ) := by
  classical
  exact {p | p ∈ stdSimplex ℝ S ∧ (∀ s, q s = 0 → p s = 0) ∧
    (∑ s, if 0 < q s then (p s - q s) ^ 2 / q s else 0) ≤ t}

/-- Extended nonnegative divergence, with 0/0 = 0 and nonzero/0 = infinity. -/
noncomputable def extendedDistance {S : Type*} [Fintype S]
    (p q : S → ℝ) : ENNReal := by
  classical
  exact ∑ s, if q s = 0 then (if p s = 0 then 0 else ⊤)
    else ENNReal.ofReal ((p s - q s) ^ 2 / q s)

noncomputable def clippedMultiplier {S : Type*} (v : S → ℝ) (α : ℝ) : S → ℝ :=
  fun s => max (v s - α) 0

noncomputable def scalarObjective {S : Type*} [Fintype S]
    (q : S → ℝ) (t : ℝ) (v : S → ℝ) (α : ℝ) : ℝ :=
  dualObj q t v (clippedMultiplier v α)

def intervalVariance (a b c α : ℝ) : ℝ := c + b * α ^ 2 - (a + b * α) ^ 2

noncomputable def intervalObjective (t a b c α : ℝ) : ℝ :=
  a + b * α - Real.sqrt (t * intervalVariance a b c α)

/-- The corrected polynomial, including its b² factor. -/
def stationaryPolynomial (t a b c α : ℝ) : ℝ :=
  b ^ 2 * intervalVariance a b c α - t * b ^ 2 * ((1 - b) * α - a) ^ 2

end RobustDP.ChiSquareAudit


