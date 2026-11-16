-- Prove2me | Definitions.Def_OnlineSteinitz_Reduction_Supplement_Rectangles
-- name    : OnlineSteinitz_Reduction_Supplement_Rectangles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:15:47.216281+00:00
-- url     : https://prove2.me/theorems/3baf0a6e-c080-4a2c-8520-2085eb538402
-- title:
--   Restricted rectangle discrepancy and Lebesgue energy
-- statement:
--   For $N$ points $(u_i,v_i)$, allowing repeated points, define the anchored rectangle discrepancy by
--
--   $$D(x,y)=\#\{i:u_i<x,\ v_i<y\}-Nxy.$$
--
--   An interval union is a union of arbitrary real intervals with any endpoint conventions, interpreted as Lebesgue measurable as required by the source's length and integral notation. There is no finite, countable, equal-width or dyadic restriction on the interval collection. Completed Lebesgue measurability is used, without a Borel-set restriction. The restricted energy is the nonnegative Lebesgue integral of $D(x,y)^2$ over $E\times[0,1]$. It is represented in the extended nonnegative reals to avoid default values for nonintegrable real integrals. In the claim's domain $E\subseteq[0,1]$, the integrand is bounded by $N^2$ and the area by one, so this equals the ordinary finite squared-discrepancy integral.
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf; SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366; Claim 5.6, pp.24–26

import Mathlib

open MeasureTheory
open scoped BigOperators ENNReal

namespace OnlineSteinitz.Reduction.Supplement

/-! Claim 5.6, p.24. Intervals include all endpoint conventions.
Lebesgue measurability is the convention implicit in |E| and integration over E;
NullMeasurableSet uses the completed Lebesgue sigma algebra, not just Borel sets.
No finite/countable/dyadic restriction on the interval collection is imposed. -/
def IntervalUnion (E : Set ℝ) : Prop :=
  NullMeasurableSet E volume ∧
  ∃ intervals : Set (Set ℝ), E = ⋃₀ intervals ∧
    ∀ I ∈ intervals, Set.OrdConnected I

noncomputable def rectangleDiscrepancy {N : ℕ} (pts : Fin N → ℝ × ℝ)
    (x y : ℝ) : ℝ :=
  ((Finset.univ.filter (fun i => (pts i).1 < x ∧ (pts i).2 < y)).card : ℝ) -
    N * x * y

/-! Nonnegative Lebesgue integration prevents a nonintegrable Bochner
integral from silently becoming zero. For E ⊆ [0,1] the integrand is bounded
by N² and the domain has finite area, so this is the usual finite integral. -/
noncomputable def restrictedEnergy {N : ℕ} (pts : Fin N → ℝ × ℝ)
    (E : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ x in E, ∫⁻ y in Set.Icc (0 : ℝ) 1,
    ENNReal.ofReal ((rectangleDiscrepancy pts x y) ^ 2)

end OnlineSteinitz.Reduction.Supplement


