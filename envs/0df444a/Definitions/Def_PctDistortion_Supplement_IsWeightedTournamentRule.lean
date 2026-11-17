-- Prove2me | Definitions.Def_PctDistortion_Supplement_IsWeightedTournamentRule
-- name    : PctDistortion_Supplement_IsWeightedTournamentRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:28:17.410344+00:00
-- url     : https://prove2.me/theorems/605e9ab5-f8f8-4cf3-9ad0-25cb66f46872
-- title:
--   Weighted tournament rules
-- statement:
--   For an election $\mathcal E=(V,\mathcal C,\vec\succ)$ and candidates $c,c'$, the **pairwise vote count** is $\#\{v\in V\mid c\succ_v c'\}$.
--
--   A **weighted tournament rule** is a randomized voting rule that receives only the pairwise vote counts instead of the full election: whenever two elections $\mathcal E,\mathcal E'$ on the same candidate set have
--   $$\#\{v\in V\mid c\succ_v c'\}=\#\{v'\in V'\mid c\succ'_{v'} c'\}\quad\text{for all }c,c',$$
--   the rule returns the same lottery on both.
--
--   Many classical rules (Copeland, Kemeny, Ranked Pairs, Schulze, C1- and C2-Maximal Lotteries, ABC Maximal Lotteries) are weighted tournament rules; Theorem 8 gives a lower bound for the whole class.
--
--   **Formalization Note** The two elections may have different voter types; when there are at least two candidates the counts determine the number of voters. Nothing else is required of the rule.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), footnote 3, p.3; §7.2, p.23

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_Supplement_IsRandomizedRule

set_option autoImplicit false

namespace PctDistortion.Supplement

open PctDistortion

open Classical in
/-- The **pairwise vote count** `#{v ∈ V | c ≻_v c'}`: the number of voters who rank `c` above
`c'`. -/
noncomputable def pairCount {V C : Type} [Fintype V] (E : Election V C) (c c' : C) : ℕ :=
  (Finset.univ.filter (fun v => E.prefers v c c')).card

/-- `A` is a **weighted tournament rule**: a randomized voting rule that receives only the
pairwise vote counts, i.e. whose output on an election depends only on the numbers
`#{v | c ≻_v c'}` for all pairs of candidates `c, c'`. Two elections on the same candidate type
with the same pairwise counts get the same lottery.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), footnote 3, p.3 and §7.2, p.23: "a weighted tournament rule [42] is a voting rule which
receives only the pairwise victory margins for each pair of candidates instead of the full election
E; that is, it learns, for each pair c, c′ of candidates, the number of voters v ranking c ≻v c′."

**Formalization Note.** The two elections may have different voter types (the counts determine
the number of voters when there are two or more candidates). Nothing else (neutrality,
anonymity) is required. -/
def IsWeightedTournamentRule (A : VotingRule) : Prop :=
  IsRandomizedRule A ∧
    ∀ (V V' C : Type) [Fintype V] [Nonempty V] [Fintype V'] [Nonempty V'] [Fintype C]
      [Nonempty C] (E : Election V C) (E' : Election V' C),
      (∀ c c', pairCount E c c' = pairCount E' c c') → A V C E = A V' C E'

end PctDistortion.Supplement


