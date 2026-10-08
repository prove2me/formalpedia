-- Prove2me | Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm
-- name    : OnlineStochMatching_SuggestedMatching_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:47:27.614988+00:00
-- url     : https://prove2.me/theorems/aa8743c6-6645-4a7c-a4c7-23a6b8cec1a4
-- title:
--   Suggested matching algorithm and complete-graph family
-- statement:
--   Fix any maximum integral expected-instance matching $M$ and any valid labelling of its selected advertisers to distinct copies of each type. On each arrival, independently select a copy uniformly from all $n$ copies. The copy determines both the arriving type and either its labelled ad or no ad. An ad is assigned only on its first selection; later selections of the same ad make no assignment. Thus
--
--   $$\mathrm{ALG}(\omega)=|\{a\in A:\text{$a$ is selected at least once in }\omega\}|.$$
--
--   The module also defines the uniform run probability, expected assignment count, and the complete bipartite family with $A=I=\{0,\ldots,n-1\}$ and $e_i=1$ used for tightness.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, pp. 5–6, §4.1, Online Algorithm and Tightness of the Analysis

import Definitions.Def_OnlineStochMatching_SuggestedMatching_Instance
import Definitions.Def_OnlineStochMatching_SuggestedMatching_BallsInBins

namespace OnlineStochMatching.SuggestedMatching

variable {A I : Type} [Fintype A] [Fintype I]

/-- The suggested matching algorithm's output: each labelled advertiser is assigned
on its first selection, so the output is the number of distinct selected ads. -/
noncomputable def algorithm (inst : Instance A I) (label : inst.Copy → Option A)
    (ω : Fin inst.n → inst.Copy) : ℕ := by
  classical
  exact (Finset.univ.filter fun a : A => ∃ t, label (ω t) = some a).card

/-- Probability of an event under independent uniform copy draws. -/
noncomputable def runProbability (inst : Instance A I)
    (P : (Fin inst.n → inst.Copy) → Prop) : ℝ := uniformProbability P

/-- Expected number of assignments by the suggested matching algorithm. -/
noncomputable def expectedAlgorithm (inst : Instance A I) (label : inst.Copy → Option A) : ℝ :=
  uniformExpectation (fun ω : Fin inst.n → inst.Copy => (algorithm inst label ω : ℝ))

/-- The complete bipartite instance with `n` advertisers, `n` types, and `e_i = 1`. -/
def completeInstance (n : ℕ) (hn : 0 < n) : Instance (Fin n) (Fin n) where
  E := Finset.univ
  e := fun _ => 1
  n := n
  n_eq := by simp
  n_pos := hn

end OnlineStochMatching.SuggestedMatching


