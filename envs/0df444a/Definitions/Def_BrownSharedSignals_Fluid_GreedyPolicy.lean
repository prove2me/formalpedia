-- Prove2me | Definitions.Def_BrownSharedSignals_Fluid_GreedyPolicy
-- name    : BrownSharedSignals_Fluid_GreedyPolicy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:52:19.048473+00:00
-- url     : https://prove2.me/theorems/90868665-93c5-4ea8-9e7a-4f3b9228ce6e
-- title:
--   Local priority indices, feasible greedy repair and performance comparisons
-- statement:
--   A priority index assigns each project a real score depending only on its own state, action, current signal and time. Scores have no ties on admissible joint actions. Projects are sorted in decreasing score. Given independent fluid proposals, the greedy repair scans every project, accepts its proposed action if the actual consumption fits the remaining budget, and otherwise leaves its action at zero and continues. It does not stop at the first rejection. The repaired mixed policy is the push-forward of the proposal law under this deterministic repair.
--
--   Action and state mismatch counts compare coordinates of two vectors. The telescoping summand includes the Lagrangian resource penalty, the reward difference and the two next-state expectations. The comparison policy is evaluated at the same state and complete signal-history memory as the proposal; its own randomization is averaged explicitly.
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), Definitions 4.2–4.3, printed 20–21 / PDF 21–22; Appendix EC4, printed EC-12–EC-13 / PDF 50–51

import Definitions.Def_BrownSharedSignals_Fluid_FluidLP

open scoped BigOperators
noncomputable section

namespace BrownSharedSignals.Fluid
variable {N T : ℕ}

/-- Definition 4.2: scores use only the local state, signal, action, project and time.
No dependence on other projects' states is hidden in the ordering. -/
structure Priority (M : Model N T) where
  score : (t : ℕ) → (i : Fin N) → Fin (M.stateSize i+1) → Signal M → ℝ → ℝ
  no_ties : ∀ t s z (a : Actions M t s z) i j, i ≠ j →
    score t i (s i) z (a i).val ≠ score t j (s j) z (a j).val

def priorityOrder (M : Model N T) (v : Priority M) (t : ℕ) (s : State M) (z : Signal M)
    (a : Fin N → ℝ) : List (Fin N) := by
  classical
  exact (Finset.univ.toList).mergeSort (fun i j => decide (v.score t i (s i) z (a i) ≥ v.score t j (s j) z (a j)))

/-- Definition 4.3: scan all projects, accepting if the actual consumption fits.
A rejection leaves the budget unchanged and the scan continues. -/
def repair (M : Model N T) (v : Priority M) (t : ℕ) (s : State M) (z : Signal M)
    (a : Fin N → ℝ) : Fin N → ℝ := by
  classical
  exact ((priorityOrder M v t s z a).foldl
    (fun (acc : ℝ × (Fin N → ℝ)) i =>
      if M.consumption t i (s i) z (a i) ≤ acc.1 then
        (acc.1 - M.consumption t i (s i) z (a i), Function.update acc.2 i (a i))
      else acc) (M.budget t z, fun _ => 0)).2

/-- Push-forward of the independent proposals by the deterministic repair. -/
def repairedPolicy (M : Model N T) (p : LocalPolicy M) (v : Priority M) : Policy M := by
  classical
  exact fun t h s a => ∑ b : Actions M t s (current M h),
    independentPolicy M p t h s b *
      if repair M v t s (current M h) (actionVector M b) = actionVector M a then 1 else 0

def mismatch (a b : Fin N → ℝ) : ℝ := by
  classical
  exact ∑ i, if a i = b i then 0 else 1

def stateMismatch (M : Model N T) (s s' : State M) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => s i ≠ s' i)).card

/-- Source telescoping summand, including the penalty and both next-state
expectations. π is evaluated at the same state and history as the ρ proposal. -/
def telescopingSummand (M : Model N T) (lam : Multiplier M) (π : Policy M)
    (t : ℕ) (h : History M t) (s : State M) (a : Actions M t s (current M h)) : ℝ :=
  lam t h * (M.budget t (current M h) - consumption M t s (current M h) (actionVector M a)) +
  reward M t s (current M h) (actionVector M a) -
    (∑ b, π t h s b * reward M t s (current M h) (actionVector M b)) +
  nextExpectation M t h s (actionVector M a) (policyValue M π (t+1)) -
    (∑ b, π t h s b * nextExpectation M t h s (actionVector M b) (policyValue M π (t+1)))

end BrownSharedSignals.Fluid


