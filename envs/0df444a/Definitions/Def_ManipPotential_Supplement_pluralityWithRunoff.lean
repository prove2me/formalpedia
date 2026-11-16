-- Prove2me | Definitions.Def_ManipPotential_Supplement_pluralityWithRunoff
-- name    : ManipPotential_Supplement_pluralityWithRunoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:02:25.611011+00:00
-- url     : https://prove2.me/theorems/52ac4e70-0e68-4081-b2f2-4a7aa3cecaf7
-- title:
--   Plurality with Runoff $\mathrm{PWR}$ (parallel-universes ties)
-- statement:
--   Under **Plurality with Runoff** ($\mathrm{PWR}$), each voter gives one point to her top-ranked candidate in the first round, the two candidates with the highest scores advance to the runoff, and in the runoff the candidate preferred by more voters wins. Ties are handled by **parallel-universes tiebreaking**: $c \in \mathrm{PWR}(\succ_N)$ if some way of breaking ties makes $c$ win.
--
--   Concretely, $c \in \mathrm{PWR}(\succ_N)$ iff there is a candidate $b \ne c$ such that
--
--   1. every other candidate has at most as many top-choice votes as $c$ and as $b$ (so $\{c, b\}$ can advance), and
--   2. $|\{i : b \succ_i c\}| \le |\{i : c \succ_i b\}|$ ($c$ wins or ties the runoff).
--
--   **Formalization Note** A tied runoff makes both finalists winners; the final tie is broken by the tiebreaker $\succ_T$, like every other tie in the winner set.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.1.2, p.12

import Mathlib
import Definitions.Def_ManipPotential_Supplement_SCC
import Definitions.Def_ManipPotential_Supplement_pairCount

namespace ManipPotential.Supplement

open Classical in
/-- Plurality with Runoff `PWR`, with parallel-universes tiebreaking (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.1.2, p.12):
each voter gives one point to her top candidate; the two candidates with the highest scores advance
to a runoff, which the candidate preferred by more voters wins; `c ∈ PWR(≻_N)` if some way of
breaking ties makes `c` win.

**Formalization Note** A pair `{c, b}` (`b ≠ c`) can advance under some breaking of first-round ties
iff every other candidate has at most as many top-choice votes as `c` and as `b`. Then `c` wins the
runoff against `b` iff `|{i : b ≻_i c}| ≤ |{i : c ≻_i b}|`; a tied runoff makes both finalists
winners (the final tie is left to the tiebreaker `≻_T`). -/
noncomputable def pluralityWithRunoff {m : ℕ} : SCC m := fun P =>
  let top : Fin m → ℕ := fun x => P.countP (fun r => decide ((r x : ℕ) = 0))
  Finset.univ.filter (fun c => ∃ b : Fin m, b ≠ c ∧
    (∀ x : Fin m, x ≠ c → x ≠ b → top x ≤ top c ∧ top x ≤ top b) ∧
    pairCount P b c ≤ pairCount P c b)

end ManipPotential.Supplement


