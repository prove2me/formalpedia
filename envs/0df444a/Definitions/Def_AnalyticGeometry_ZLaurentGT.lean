-- Prove2me | Definitions.Def_AnalyticGeometry_ZLaurentGT
-- name    : AnalyticGeometry_ZLaurentGT
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T13:08:30.263111+00:00
-- url     : https://prove2.me/theorems/b63e8f17-0e94-4b0a-881f-e8c234a9ce09
-- title:
--   The ring $\mathbb{Z}((T))_{>r}$ of overconvergent integral Laurent series
-- statement:
--   This bundle fixes the objects of the mission.
--
--   An **integral Laurent series** is an element of $\mathbb{Z}((T))$, modelled as a Hahn series with
--   exponents in $\mathbb{Z}$ and coefficients in $\mathbb{Z}$: a family $(a_n)_{n \in \mathbb{Z}}$ of
--   integers whose support is bounded below, written $f = \sum_{n \gg -\infty} a_n T^n$.
--
--   For a real number $s$, the **decay condition at radius $s$** is
--   $$\lim_{n \to +\infty} |a_n|\, s^{\,n} = 0 .$$
--
--   For a real number $r$, the ring of the lecture is
--   $$\mathbb{Z}((T))_{>r} = \Big\{\, f = \sum_{n \gg -\infty} a_n T^n \;\Big|\; \exists\, s > r,\
--   \lim_{n \to +\infty} |a_n| s^{\,n} = 0 \,\Big\},$$
--   the **overconvergent** series: those whose Laurent expansion converges on a punctured disc of some
--   radius strictly larger than $r$. It is introduced here as a subset of $\mathbb{Z}((T))$; that it is
--   a subring is the first milestone of the mission.
--
--   Finally, **evaluation** of $f$ at a real number $x$, respectively a complex number $x$, is the
--   unordered sum $\sum_{n \in \mathbb{Z}} a_n x^{\,n}$, taken over all integers $n$.
-- source:
--   Peter Scholze (all results joint with Dustin Clausen), Lectures on Analytic Geometry, Lecture VII, pp. 42-44, Theorem 7.1 (attributed there to D. Harbater, Convergent arithmetic power series, Amer. J. Math. 106 (1984), 801-846). https://www.math.uni-bonn.de/people/scholze/Analytic.pdf

import Mathlib

namespace AnalyticGeometry

open Filter Topology

/-- `DecaysAt s f` says that the coefficients `aₙ` of the integral Laurent series `f`
satisfy `|aₙ| sⁿ → 0` as `n → ∞`. -/
def DecaysAt (s : ℝ) (f : LaurentSeries ℤ) : Prop :=
  Tendsto (fun n : ℤ => |(f.coeff n : ℝ)| * s ^ n) atTop (𝓝 0)

/-- The carrier of the ring `ℤ((T))_{>r}`: those integral Laurent series
`∑_{n ≫ -∞} aₙ Tⁿ` for which there is some `s > r` with `|aₙ| sⁿ → 0`. -/
def zLaurentGT (r : ℝ) : Set (LaurentSeries ℤ) :=
  {f : LaurentSeries ℤ | ∃ s > r, DecaysAt s f}

/-- Evaluation of an integral Laurent series at a real number `x`:
the unordered sum `∑' n : ℤ, aₙ xⁿ`. -/
noncomputable def evalR (x : ℝ) (f : LaurentSeries ℤ) : ℝ :=
  ∑' n : ℤ, (f.coeff n : ℝ) * x ^ n

/-- Evaluation of an integral Laurent series at a complex number `x`:
the unordered sum `∑' n : ℤ, aₙ xⁿ`. -/
noncomputable def evalC (x : ℂ) (f : LaurentSeries ℤ) : ℂ :=
  ∑' n : ℤ, (f.coeff n : ℂ) * x ^ n

end AnalyticGeometry


