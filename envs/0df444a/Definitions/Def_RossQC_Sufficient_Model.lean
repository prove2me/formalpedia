-- Prove2me | Definitions.Def_RossQC_Sufficient_Model
-- name    : RossQC_Sufficient_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:19.23631+00:00
-- url     : https://prove2.me/theorems/f1510ae1-fbcf-41d6-ad56-ee1b9ec6cf02
-- title:
--   §3 two-state quality-control model, Bellman alternatives, value iteration and threshold rules
-- statement:
--   The underlying production process has a good state and a bad state. Let $P\in[0,1]$ be the probability of the bad state, $\pi$ the chance that a good process deteriorates in one period, and $\beta$ the discount factor. Producing without inspection costs $CP$ in expectation; inspection costs $I$ and reveals the current state; revision costs $R$ and resets the next belief to $\pi$. The belief after producing without inspection is $T(P)=P+\pi-\pi P$.
--
--   For a continuation cost $V$, the one-step costs of producing, inspecting and revising are respectively
--   $$
--   CP+\beta V(T(P)),\qquad I+\beta P V(1)+\beta(1-P)V(\pi),\qquad R+\beta V(\pi).
--   $$
--   Starting with $V^0=0$, finite-horizon value iteration takes the minimum of these three costs at each stage, and $V_\beta(P)$ is its limit. A three-region rule produces below $P_1$, inspects from $P_1$ to $P_2$, and revises from $P_2$ onward. A two-region rule produces below $P_1$ and revises thereafter.
--
--   This model supplies the common data and conventions for the sufficient-condition results of §3. At threshold equality, the rule chooses the later action.
--
--   **Formalization Note** The threshold rules are defined for every real $P$; all optimality claims restrict them to $P\in[0,1]$. The convergence of $V^n$ is asserted in the separate equation (3) item.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, pp. 588–590, §2–§3, equations (3)–(4)

import Mathlib
import Definitions.Def_RossQC_Regions_Model
open Filter

namespace RossQC.Sufficient

/-- Ross, *Quality Control under Markovian Deterioration*, §3, p. 590.
`P` is the probability of the bad state; the parameters satisfy the standing
assumptions in the theorem statements. -/
structure Model where
  β : ℝ
  π : ℝ
  C : ℝ
  I : ℝ
  R : ℝ

/-- Ross, §3, p. 590: `TP = P + π − πP`. -/
def Model.T (M : Model) (P : ℝ) : ℝ := P + M.π - M.π * P

/-- Ross, §3, equation (3), p. 590: the cost of each action followed by
continuation value `V`. Inspection reveals the current state; revision resets
the next belief to `π`. -/
def Model.rhs3 (M : Model) (V : ℝ → ℝ) (P : ℝ) : RossQC.Regions.Action → ℝ
  | .produce => M.C * P + M.β * V (M.T P)
  | .inspect => M.I + M.β * P * V 1 + M.β * (1 - P) * V M.π
  | .revise => M.R + M.β * V M.π

/-- Ross, §3, equation (4), p. 590. Stage zero has zero cost, and stage one
is `min {CP, I, R}`. -/
def Model.valueIter (M : Model) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, P => min (M.rhs3 (M.valueIter n) P .produce)
      (min (M.rhs3 (M.valueIter n) P .inspect)
           (M.rhs3 (M.valueIter n) P .revise))

/-- Ross, §2, p. 589 and §3, equation (4), p. 590. The discounted value is
the limit of finite-horizon values; convergence is asserted in the theorem
for equation (3). -/
noncomputable def Model.value (M : Model) (P : ℝ) : ℝ :=
  limUnder atTop (fun n => M.valueIter n P)

/-- Ross, Theorem 3.7(a), p. 592. At a threshold equality the later action
is chosen. A threshold above one gives an empty revise interval on `[0,1]`. -/
noncomputable def Model.threeRegion (_M : Model) (P₁ P₂ P : ℝ) : RossQC.Regions.Action :=
  if P < P₁ then .produce else if P < P₂ then .inspect else .revise

/-- Ross, Theorem 3.7(b), p. 592. A threshold above one produces everywhere
on the admissible belief interval. -/
noncomputable def Model.twoRegion (_M : Model) (P₁ P : ℝ) : RossQC.Regions.Action :=
  if P < P₁ then .produce else .revise

end RossQC.Sufficient


