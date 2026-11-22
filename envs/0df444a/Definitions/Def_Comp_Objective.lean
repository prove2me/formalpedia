-- Prove2me | Definitions.Def_Comp_Objective
-- name    : Comp_Objective
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:33:42.619741+00:00
-- url     : https://prove2.me/theorems/2e097c77-d3a4-4d1f-9d14-8a57e799798e
-- title:
--   Objective
-- statement:
--   Definitions and structural lemmas for Objective, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Objective.lean

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_Reach
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
set_option autoImplicit true
namespace Comp
inductive Objective (S : Type*) where
  /-- Sure safety: stay inside `region` forever, with certainty (`CSG.G`). -/
  | sureSafe (region : Finset S)
  /-- Almost-sure reachability of `target` (`CSG.AF`). -/
  | almostReach (target : Finset S)
  /-- Limit-sure reachability of `target` (`CSG.LF`) -- the value-1 set. -/
  | limitReach (target : Finset S)
  /-- Quantitative probability of reaching `target` (`CSG.reachOp`'s least fixed point). -/
  | reach (target : Finset S)
  /-- Optimal discounted value at discount `l` (`DiscountedCSG.vOpt`). The discount is part of the
      question, not of the model. -/
  | discounted (l : ℚ)
inductive Answer (S : Type*) where
  /-- An exactly identified set of states. -/
  | region (c : Finset S)
  /-- A pair of sound bounds on a value vector, not claimed to be tight. -/
  | interval (lo hi : S → ℚ)
  /-- A vector within `eps` of the true value, in sup distance. -/
  | approx (v : S → ℚ) (eps : ℚ)
namespace CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
def RewardFree (G : CsgQ S A1 A2) : Prop := ∀ s a1 a2, G.r s a1 a2 = 0
instance (G : CsgQ S A1 A2) : Decidable G.RewardFree := by
  unfold RewardFree
  infer_instance
def withDiscount (G : CsgQ S A1 A2) (l : ℚ) : DiscountedCsgQ S A1 A2 where
  toCsgQ := G
  l := l
theorem withDiscount_wf (G : CsgQ S A1 A2) (h : G.WellFormed) {l : ℚ} (hl0 : 0 ≤ l)
    (hl1 : l < 1) : (G.withDiscount l).WellFormed :=
  ⟨h, hl0, hl1⟩
inductive Answers (G : CsgQ S A1 A2) (h : G.WellFormed) : Objective S → Answer S → Prop where
  /-- `c` is exactly the sure-safety region for `region`. -/
  | sureSafe {region c : Finset S} (hG : (G.toCSG h).G ↑region = (↑c : Set S)) :
      Answers G h (Objective.sureSafe region) (Answer.region c)
  /-- `c` is exactly the almost-sure reachability set for `target`. -/
  | almostReach {target c : Finset S} (hAF : (G.toCSG h).AF ↑target = (↑c : Set S)) :
      Answers G h (Objective.almostReach target) (Answer.region c)
  /-- `c` is exactly the limit-sure reachability set for `target` -- the value-1 set. -/
  | limitReach {target c : Finset S} (hLF : (G.toCSG h).LF ↑target = (↑c : Set S)) :
      Answers G h (Objective.limitReach target) (Answer.region c)
  /-- `lo` and `hi` sandwich the reachability value. Reward-freeness is a hypothesis of *this*
      constructor rather than of the objective, which is why `Answers` is a relation. -/
  | reach {target : Finset S} {lo hi : S → ℚ} (hrf : G.RewardFree)
      (h0 : ∀ s, 0 ≤ lo s) (h1 : ∀ s, lo s ≤ 1) (k0 : ∀ s, 0 ≤ hi s) (k1 : ∀ s, hi s ≤ 1)
      (hlo : castIcc lo h0 h1
        ≤ ((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)).lfp)
      (hhi : ((G.toCSG h).reachOp (· ∈ target) (toCSG_r_zero G h hrf)).lfp
        ≤ castIcc hi k0 k1) :
      Answers G h (Objective.reach target) (Answer.interval lo hi)
  /-- `v` is within `eps` of the optimal discounted value. The discount bounds are hypotheses here
      for the same reason reward-freeness is above. -/
  | discounted {l : ℚ} {v : S → ℚ} {eps : ℚ} (hl0 : 0 ≤ l) (hl1 : l < 1)
      (hd : 2 * dist (fun s => ((v s : ℚ) : ℝ))
          ((G.withDiscount l).toDiscountedCSG (withDiscount_wf G h hl0 hl1)).vOpt
        < ((eps : ℚ) : ℝ)) :
      Answers G h (Objective.discounted l) (Answer.approx v eps)
end CsgQ
end Comp


