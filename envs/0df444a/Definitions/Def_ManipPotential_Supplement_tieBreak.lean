-- Prove2me | Definitions.Def_ManipPotential_Supplement_tieBreak
-- name    : ManipPotential_Supplement_tieBreak
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:54:32.051198+00:00
-- url     : https://prove2.me/theorems/7cc30fec-7045-44f4-bc3f-5d270eab2792
-- title:
--   Tie-broken rule $F_T(\succ_N) = \mathrm{top}_{\succ_T} F(\succ_N)$
-- statement:
--   Let $F$ be an SCC and $\succ_T \in \mathcal L(C)$ a linear **tiebreaker**. The social choice function $F_T$ maps a profile $\succ_N$ to the candidate of $F(\succ_N)$ that $\succ_T$ ranks highest:
--   $$F_T(\succ_N) := \mathrm{top}_{\succ_T} F(\succ_N).$$
--
--   This is how the paper extends $k$-augmentation strategyproofness and the manipulation potential from social choice functions to SCCs.
--
--   **Formalization Note** The paper never applies $\mathrm{top}_{\succ_T}$ to an empty set. In Lean, if $F(\succ_N) = \emptyset$ the value is $\mathrm{top}_{\succ_T} C$, the tiebreaker's first candidate. Every concrete rule of the mission returns a nonempty set on every profile, so this convention matters only for the general SCCs of Theorem 4.13.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 3, "Tie(breaker)s", p.10

import Mathlib
import Definitions.Def_ManipPotential_Ranking_top
import Definitions.Def_ManipPotential_Supplement_SCC

namespace ManipPotential.Supplement

/-- The tie-broken social choice function `F_T(≻_N) := top_{≻_T} F(≻_N)` of an SCC `F` with linear
tiebreaker `≻_T ∈ L(C)` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 3, "Tie(breaker)s", p.10): among the winners, the one
ranked highest by `T`.

**Formalization Note** The winner of smallest position in `T` is `T⁻¹(min T(F P))`. The paper never
applies `top_T` to an empty winner set; here, if `F P = ∅`, the value is `top_T C`, the candidate `T`
ranks first. Every concrete rule of the mission returns a nonempty set on every profile. -/
def tieBreak {m : ℕ} [NeZero m] (F : SCC m) (T : Ranking m) : List (Ranking m) → Fin m :=
  fun P => if h : (F P).Nonempty then T.symm (((F P).image T).min' (h.image T)) else Ranking.top T

end ManipPotential.Supplement


