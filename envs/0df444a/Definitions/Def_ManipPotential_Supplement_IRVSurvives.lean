-- Prove2me | Definitions.Def_ManipPotential_Supplement_IRVSurvives
-- name    : ManipPotential_Supplement_IRVSurvives
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:03:27.190885+00:00
-- url     : https://prove2.me/theorems/01caa2f3-15c3-45b3-a2e3-3e8a11c9160c
-- title:
--   Instant Runoff elimination sequences
-- statement:
--   For a profile $\succ_N$, a set $R$ of remaining candidates and a candidate $c$, **$c$ survives from $R$** if some sequence of eliminations, each removing a candidate of minimal Instant Runoff score among the currently remaining ones, ends with $c$ as the last remaining candidate.
--
--   This encodes parallel-universes tiebreaking for Instant Runoff: every way of breaking ties among the lowest-scoring candidates is allowed.
--
--   **Formalization Note** An inductive predicate: from $\{c\}$ the survivor is $c$; from $R$ with at least two candidates, any $x \in R$ of minimal score may be eliminated, and one continues from $R \setminus \{x\}$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.1.2, p.12

import Mathlib
import Definitions.Def_ManipPotential_Supplement_irvScore

namespace ManipPotential.Supplement

/-- `IRVSurvives P R c`: starting from the remaining set `R`, some sequence of eliminations, each
removing a candidate of minimal Instant Runoff score in the current remaining set, leaves `c` as the
last candidate (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.1.2, p.12, parallel-universes tiebreaking).

**Formalization Note** Inductive: `{c}` leaves `c`; from `R` with at least two candidates, any `x ∈ R`
of minimal `irvScore P R` may be eliminated. -/
inductive IRVSurvives {m : ℕ} (P : List (Ranking m)) : Finset (Fin m) → Fin m → Prop
  | last (c : Fin m) : IRVSurvives P {c} c
  | elim (R : Finset (Fin m)) (c x : Fin m) (hx : x ∈ R) (hcard : 2 ≤ R.card)
      (hmin : ∀ y ∈ R, irvScore P R x ≤ irvScore P R y)
      (hrest : IRVSurvives P (R.erase x) c) : IRVSurvives P R c

end ManipPotential.Supplement


