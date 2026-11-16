-- Prove2me | Definitions.Def_ManipPotential_Supplement_posScore
-- name    : ManipPotential_Supplement_posScore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:56:44.90345+00:00
-- url     : https://prove2.me/theorems/80a678fd-5301-48d7-b839-d4c3a57722b8
-- title:
--   Total positional score of a candidate
-- statement:
--   For a scoring vector $s$, a profile $\succ_N$ and a candidate $c$, the **total score** of $c$ is
--   $$\mathrm{score}_s(\succ_N, c) = \sum_{i \in N} s_{\ell_i(c)},$$
--   where $\ell_i(c)$ is the position of $c$ in $\succ_i$: each voter contributes $s_\ell$ points to her $\ell$-th ranked candidate.
--
--   **Formalization Note** With 0-based positions the ballot $r$ gives $c$ the entry of $s$ at index $r(c)$, which is the paper's $s_{r(c)+1}$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Definition 3, p.15

import Mathlib
import Definitions.Def_ManipPotential_Ranking

namespace ManipPotential.Supplement

/-- The total score of candidate `c` under the positional scoring vector `s` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Definition 3,
p.15): each voter contributes `s_ℓ` points to the candidate she ranks `ℓ`-th.

**Formalization Note** A ballot `r` places `c` at 0-based position `r c`, and `s (r c)` is the
paper's `s_{(r c) + 1}`. The sum runs over the ballots of the list profile. -/
def posScore {m : ℕ} (s : Fin m → ℝ) (P : List (Ranking m)) (c : Fin m) : ℝ :=
  (P.map (fun r => s (r c))).sum

end ManipPotential.Supplement


