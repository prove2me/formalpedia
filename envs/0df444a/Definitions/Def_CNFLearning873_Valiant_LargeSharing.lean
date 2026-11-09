-- Prove2me | Definitions.Def_CNFLearning873_Valiant_LargeSharing
-- name    : CNFLearning873_Valiant_LargeSharing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:07:59.965231+00:00
-- url     : https://prove2.me/theorems/c468cb34-9700-4914-87b1-b822a40c3591
-- title:
--   Algorithm 1 and its induced groups of rare candidates
-- statement:
--   Fix any ordering of the target clauses. Start with residual $c^*$ and no selected parts. For each target clause $c$, let $U$ be the intersection of its variables with the residual variables. When $|U|>k/(1+t)$, select the residual restricted to $U$ and remove $U$ from the residual. Signs come from the candidate.
--
--   $$\mathcal C^*_{<\tau}(\mathcal S)=\{c^*\in\mathcal C^*_{<\tau}:\operatorname{LargeSharing}(F;c^*)=\mathcal S\}.$$
--
--   Merge the compatible selected parts to form the group's root subclause. This defines the actual scan and grouping without assuming a nonempty output, a cardinality bound, or a rarity conclusion.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, Algorithm 1 and grouping, pp.15–16 (PDF pp.15–16)

import Definitions.Def_CNFLearning873_Valiant_Thresholds

namespace CNFLearning873.Valiant

/-- Algorithm 1, p.15 = PDF p.15, scanned in the given fixed target-clause order.
The residual and selected parts carry the candidate's signs, never the target's. -/
noncomputable def largeSharing {n : ℕ} (k : ℕ) (t : ℝ) :
    List (Clause n) → Clause n → CNF n
  | [], _ => ∅
  | c :: cs, residual => by
      classical
      let U := support residual ∩ support c
      exact if (k : ℝ) / (1 + t) < (U.card : ℝ) then
        insert (restrict residual U)
          (largeSharing k t cs (restrict residual (support residual \ U)))
      else largeSharing k t cs residual

/-- Group by the entire selected collection, as a set, rather than its scan history. -/
noncomputable def sharingGroup {n : ℕ} (F : CNF n) (h : (solutions F).Nonempty)
    (k d : ℕ) (t ε : ℝ) (order : List (Clause n)) (S : CNF n) : CNF n := by
  classical
  exact (rare F h k d t ε).filter fun c => largeSharing k t order c = S

/-- Merge the compatible selected parts. On incompatible input true wins, but all
source uses are actual LargeSharing outputs and compatibility is to be established. -/
noncomputable def mergeParts {n : ℕ} (S : CNF n) : Clause n := by
  classical
  exact fun v => if ∃ c ∈ S, c v = some true then some true
    else if ∃ c ∈ S, c v = some false then some false else none

end CNFLearning873.Valiant


