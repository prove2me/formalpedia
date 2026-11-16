-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_contractTime
-- name    : MaxMinFracSched_Supplement_contractTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:14:58.518196+00:00
-- url     : https://prove2.me/theorems/cf5955bc-1794-4a6e-98e9-4eac998b1ac0
-- title:
--   Contraction of the time axis by all densest intervals, $\tau_{I^\star}$
-- statement:
--   Let $U$ be the union of all densest intervals of $J$. The **contraction map** is
--   $$
--   \tau(t)=t-\bigl|U\cap(-\infty,t]\bigr|,
--   $$
--   where $|\cdot|$ is Lebesgue measure. It collapses every densest interval to a point and shifts each later time to the left by the total length removed before it.
--
--   For a single interval $I=[L,R]$ this is the map $\tau_I$ of Definition 7.2: $\tau_I(t)=t$ for $t<L$, $\tau_I(t)=L$ for $L\le t\le R$, and $\tau_I(t)=t-|I|$ for $t>R$.
--
--   **Formalization Note** Theorem 7.3 contracts all of $I^{\star}$ at once. The maximal densest intervals are finitely many, pairwise disjoint and separated by gaps of positive length, so contracting them one after another gives this map. For a valid instance with $\rho^\star>0$ the set $U$ is bounded and the measure is finite.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Definition 7.2, p.33 (PDF p.35); Theorem 7.3, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_Supplement_IsDensestInterval

namespace MaxMinFracSched

namespace Supplement

/-- **The contraction of the time axis by all densest intervals, `τ_{I⋆}`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Definition 7.2 (Contracted instance), p.33 (PDF p.35): "τI(t) = t for t < L, L for
L ≤ t ≤ R, t − |I| for t > R"; Theorem 7.3, p.34 (PDF p.36): "the contracted instance J−I⋆".

With `U` the union of all densest intervals `[L, R]` of `J`, `contractTime J t = t − |U ∩ (−∞, t]|`
(Lebesgue measure): every densest interval is collapsed to a point and later times are shifted left
by the total length removed before them.

**Formalization Note.** Definition 7.2 contracts one interval `I`; Theorem 7.3 contracts all of
`I⋆`. `U` is the finite disjoint union of the maximal densest intervals, which are separated by
gaps of positive length, so contracting them one after the other gives this map; for a single
densest interval `I` it is `τ_I`. For a valid instance with `ρ⋆ > 0` the set `U` is bounded, so the
measure is finite. -/
noncomputable def contractTime (J : Finset Job) (t : ℝ) : ℝ :=
  t - (MeasureTheory.volume
    ((⋃ (L : ℝ) (R : ℝ) (_ : IsDensestInterval J L R), Set.Icc L R) ∩ Set.Iic t)).toReal

end Supplement

end MaxMinFracSched


