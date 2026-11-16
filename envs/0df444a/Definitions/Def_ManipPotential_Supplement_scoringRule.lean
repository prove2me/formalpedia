-- Prove2me | Definitions.Def_ManipPotential_Supplement_scoringRule
-- name    : ManipPotential_Supplement_scoringRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:57:18.624834+00:00
-- url     : https://prove2.me/theorems/11dc59a0-f49a-403e-8fae-cc28e4c21f86
-- title:
--   Positional scoring rule $F^s$
-- statement:
--   The **positional scoring rule** $F^s$ associated with a scoring vector $s$ returns, on a profile $\succ_N$, the candidates of highest total score:
--   $$F^s(\succ_N) = \{ c \in C : \mathrm{score}_s(\succ_N, c') \le \mathrm{score}_s(\succ_N, c) \text{ for all } c' \in C \}.$$
--
--   Plurality and Borda Count are the scoring rules of $(1,0,\dots,0)$ and of the normalized Borda vector.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Definition 3, p.15

import Mathlib
import Definitions.Def_ManipPotential_Supplement_SCC
import Definitions.Def_ManipPotential_Supplement_posScore

namespace ManipPotential.Supplement

open Classical in
/-- The positional scoring rule `F^s` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Definition 3, p.15): on a profile, the candidates of
highest total score.

**Formalization Note** `F^s(P) = {c : score(c) ≥ score(c') for all c'}`; nonempty whenever `m ≥ 1`. -/
noncomputable def scoringRule {m : ℕ} (s : Fin m → ℝ) : SCC m :=
  fun P => Finset.univ.filter (fun c => ∀ c', posScore s P c' ≤ posScore s P c)

end ManipPotential.Supplement


