-- Prove2me | Definitions.Def_SoSLinAlg_WeakRank_SoSRefutable
-- name    : SoSLinAlg_WeakRank_SoSRefutable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T22:29:51.544655+00:00
-- url     : https://prove2.me/theorems/abc2be99-5fb2-4e90-bb85-713b54407131
-- title:
--   Degree-bounded sum-of-squares refutation
-- statement:
--   Let $p_i$ be a finite family of real polynomials in an arbitrary set of indeterminates and let $D\ge0$ be an integer. The predicate $\operatorname{SoSRefutable}(p,D)$ means that there are polynomials $g$ and $h_i$ such that
--   $$-1=g+\sum_i h_i p_i,\qquad g\text{ is a sum of polynomial squares},\qquad \deg g\le D,\qquad \deg(h_i p_i)\le D\ \text{for every }i.$$
--   The degree bound applies separately to each product, and to $g$ itself. The empty sum of squares is permitted. The variables are unrestricted real variables.
--
--   This is the reusable certificate notion shared by all systems in the mission. A finite index type presents the equations; no positivity, Boolean, or boundedness hypotheses are built into the system. Mathlib assigns total degree zero to the zero polynomial; for the natural bound $D$ this admits exactly the same polynomials as the source's degree-minus-infinity convention.
-- source:
--   Dmitriy Kunisky, Xifan Yu, The sum-of-squares complexity of linear-algebraic principles, STOC 2027 submission #1181 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1181.pdf, Definition 1.1 and proof conventions, PDF p.4 (printed p.2)

import Mathlib

namespace SoSLinAlg.WeakRank

/-- Definition 1.1, PDF p.4 (printed p.2). The bounds are on each product and on
 the sum-of-squares polynomial itself. Zero has totalDegree 0, harmless for D : ℕ. -/
def SoSRefutable {σ ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℝ) (D : ℕ) : Prop :=
  ∃ (g : MvPolynomial σ ℝ) (h : ι → MvPolynomial σ ℝ),
    IsSumSq g ∧ g.totalDegree ≤ D ∧
    (∀ i, (h i * p i).totalDegree ≤ D) ∧
    (-1 : MvPolynomial σ ℝ) = g + ∑ i, h i * p i

end SoSLinAlg.WeakRank


