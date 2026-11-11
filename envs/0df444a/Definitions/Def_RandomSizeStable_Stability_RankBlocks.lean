-- Prove2me | Definitions.Def_RandomSizeStable_Stability_RankBlocks
-- name    : RandomSizeStable_Stability_RankBlocks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:09.284354+00:00
-- url     : https://prove2.me/theorems/402df957-02bb-486b-bf71-7f02c604e2e3
-- title:
--   Marked rank blocks, scanning cutoffs and maximum distance
-- statement:
--   Fix a profile $E$, lottery $P$ and voter $v$. Write $b_{v,c}$ for the total mass of candidates strictly below $c$. Candidate $c$ occupies the half-open block
--   $$I_{v,c}=[b_{v,c},b_{v,c}+P(c)).$$
--   For $H\subseteq C$, its marked region is $H_v=\bigcup_{c\in H}I_{v,c}$. A zero-mass candidate has an empty block but keeps its position in the ranking.
--
--   For any marked set, $a_v$ is the sum of masses on candidates strictly below every unmarked candidate. It is exactly the mass scanned from worst to best before the first unmarked candidate, even if that candidate has zero mass. If all candidates are marked, all mass is passed. The upper cutoff $A_v$ is the largest right endpoint of a marked block of positive length, or zero when none exists.
--
--   Given distances $d$ and a designated candidate $o$, thresholds use
--   $$H(t)=\{c:d(o,c)>t\},\qquad T=\max_{c\in C}d(o,c).$$
--   The definitions compute all cutoffs from the actual profile and lottery. No scalar cutoff inequalities or optimality conditions are built into them. The finite maximum uses a nonempty candidate type.
-- source:
--   Nisarg Shah, Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission #1342 (October 2026), p. 11–12, 14, Section 4, Ranking intervals and stability; Distance thresholds and ranking cuts.

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_Stability
import Definitions.Def_StableVotingDistortion_leftRank
import Definitions.Def_StableVotingDistortion_HasDistortionAtMost

set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable.Stability

/-- §4 p.11: half-open blocks, arranged worst to best. A zero mass block is empty,
but its candidate still has a ranking position. -/
def rankBlock {V C : Type} [Fintype C] (E : Election V C) (P : C → ℝ)
    (v : V) (c : C) : Set ℝ :=
  Set.Ico (leftRank E P v c) (leftRank E P v c + P c)

/-- §4 p.11: the union of the blocks marked by H. -/
def markedRegion {V C : Type} [Fintype C] (E : Election V C) (P : C → ℝ)
    (v : V) (H : Set C) : Set ℝ :=
  ⋃ c ∈ H, rankBlock E P v c

/-- §4 p.12: the candidates whose distance from o strictly exceeds t. -/
def marked {V C : Type} (d : V ⊕ C → V ⊕ C → ℝ) (o : C) (t : ℝ) : Set C :=
  {c | t < d (Sum.inr o) (Sum.inr c)}

/-- §4 p.12: the mass passed before the first unmarked candidate. Precisely the
candidates ranked below every unmarked candidate are passed. This definition
checks zero-mass unmarked candidates too. If all are marked it passes all mass. -/
noncomputable def lowerCut {V C : Type} [Fintype C] (E : Election V C)
    (P : C → ℝ) (v : V) (H : Set C) : ℝ := by
  classical
  exact ∑ c, if ∀ j, j ∉ H → E.prefers v j c then P c else 0

/-- §4 p.12: best positive-length marked block's right endpoint, or zero.
The maximum is over a finite nonempty candidate type. -/
noncomputable def upperCut {V C : Type} [Fintype C] [Nonempty C] (E : Election V C)
    (P : C → ℝ) (v : V) (H : Set C) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun c => if c ∈ H ∧ 0 < P c then leftRank E P v c + P c else 0)

/-- §4 p.14: finite maximum distance from the designated candidate. -/
noncomputable def maxDistance {V C : Type} [Fintype C] [Nonempty C]
    (d : V ⊕ C → V ⊕ C → ℝ) (o : C) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun c => d (Sum.inr o) (Sum.inr c))

end RandomSizeStable.Stability


