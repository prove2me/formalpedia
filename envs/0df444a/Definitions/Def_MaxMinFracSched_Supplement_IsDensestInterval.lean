-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_IsDensestInterval
-- name    : MaxMinFracSched_Supplement_IsDensestInterval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:13:29.784935+00:00
-- url     : https://prove2.me/theorems/cc237166-1630-4ea7-a710-9ac124e4d706
-- title:
--   Densest interval of an instance
-- statement:
--   An interval $[L,R]$ with $L<R$ is **densest** for the instance $J$ when its work density equals the maximum density:
--   $$
--   \rho_J([L,R])=\frac{W_J([L,R])}{R-L}=\rho^{\star}_J ,
--   $$
--   where $W_J([L,R])$ is the total work of the jobs whose windows lie in $[L,R]$ and $\rho^{\star}_J$ is the supremum of the densities of all intervals.
--
--   Densest intervals are the building blocks of the decomposition of the lexicographic optimum (Theorem 7.3).
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Definition 3.2, p.12 (PDF p.14); Theorem 7.3, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_density
import Definitions.Def_MaxMinFracSched_maxDensity

namespace MaxMinFracSched

namespace Supplement

/-- **A densest interval.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Definition 3.2, p.12 (PDF p.14): "An interval I⋆ is called densest for an instance J if it
maximizes ρJ(I) over all intervals I"; Theorem 7.3, p.33 (PDF p.35): "let I⋆ be the set of densest
intervals of J and let ρ⋆J be the density of these densest intervals".

`[L, R]` is densest for `J` when `L < R` and its density `ρ_J([L, R])` equals `ρ⋆_J = maxDensity J`. -/
def IsDensestInterval (J : Finset Job) (L R : ℝ) : Prop :=
  L < R ∧ density J L R = maxDensity J

end Supplement

end MaxMinFracSched


