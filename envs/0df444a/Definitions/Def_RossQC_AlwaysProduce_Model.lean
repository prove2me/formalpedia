-- Prove2me | Definitions.Def_RossQC_AlwaysProduce_Model
-- name    : RossQC_AlwaysProduce_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:34.080982+00:00
-- url     : https://prove2.me/theorems/bdd2867f-33aa-44a9-ba00-caa3103cf2d6
-- title:
--   Two-state deterioration model, Bellman alternatives, value iteration, and always-produce cost
-- statement:
--   In the two-state production model, $P\in[0,1]$ is the probability that the process is in the bad state. A good unit has production cost zero, a bad unit has production cost $C$, inspection costs $I$, and revision costs $R$. A good process becomes bad with probability $\pi$ per period; a bad process remains bad until revision. Future costs are discounted by $\beta$.
--
--   The belief update after production without inspection is $T(P)=P+\pi-\pi P$. For a candidate future-cost function $W$, the three Bellman alternatives are
--
--   $$
--   C P+\beta W(TP),\qquad I+\beta P W(1)+\beta(1-P)W(\pi),\qquad R+\beta W(\pi).
--   $$
--
--   Starting from $V^0=0$, finite-horizon values satisfy $V^{n+1}(P)=\min_a\operatorname{rhs}_3(V^n,P,a)$; the discounted value $V_\beta(P)$ is their limit. The cost of the rule $R^0$ that always produces without inspection is defined independently by the series $\psi(P)=\sum_{n=0}^{\infty}\beta^n C T^nP$.
--
--   These definitions fix the model shared by the theorem and its supporting results. The convergence of the limit and the closed form of the series are claims to be established by separate theorem items.
--
--   **Formalization Note** The data structure itself imposes no parameter bounds. Each theorem carries the paper's standing conditions $0<\beta<1$, $0\le\pi\le1$, and $0<C<I<R$.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, pp. 588, 590–591, §2–§3, equations (3)–(5)

import Mathlib
import Definitions.Def_RossQC_Regions_Model
open Filter

namespace RossQC.AlwaysProduce

/-- Ross, *Quality Control under Markovian Deterioration*, §3, pp. 590–591.
The two underlying states are good and bad. `P` is the probability of the bad state.
The parameter assumptions `0 < β < 1`, `0 ≤ π ≤ 1`, and `0 < C < I < R` belong
to the theorem statements, rather than being built into this data type. -/
structure Model where
  β : ℝ
  π : ℝ
  C : ℝ
  I : ℝ
  R : ℝ

/-- Ross, §3, p. 590: `TP = P + π − πP`. -/
def Model.T (M : Model) (P : ℝ) : ℝ := P + M.π - M.π * P

/-- Ross, §3, equation (3), p. 590: the three right-hand-side alternatives.
Inspection reveals the current state and leads to belief `1` or `π`; revision
leads to belief `π`. -/
def Model.rhs3 (M : Model) (V : ℝ → ℝ) (P : ℝ) : RossQC.Regions.Action → ℝ
  | .produce => M.C * P + M.β * V (M.T P)
  | .inspect => M.I + M.β * P * V 1 + M.β * (1 - P) * V M.π
  | .revise => M.R + M.β * V M.π

/-- Ross, §3, equation (4), p. 590. `valueIter 0 = 0`, so `valueIter 1`
is exactly the paper's `V_β¹ = min {CP, I, R}`. -/
def Model.valueIter (M : Model) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, P => min (M.rhs3 (M.valueIter n) P .produce)
      (min (M.rhs3 (M.valueIter n) P .inspect)
           (M.rhs3 (M.valueIter n) P .revise))

/-- Ross, §2, p. 588 and §3, equation (4), p. 590. The discounted optimal
cost is the limit of finite-horizon value iteration. Its convergence is asserted
separately, so the total-function value of `limUnder` on a divergent sequence
cannot silently establish the Bellman equation. -/
noncomputable def Model.value (M : Model) (P : ℝ) : ℝ :=
  limUnder atTop (fun n => M.valueIter n P)

/-- Ross, §3, equation (5), p. 591. The expected discounted cost of the policy
`R⁰` that always produces without inspection, defined by its infinite series,
not by the closed form derived in equation (5). -/
noncomputable def Model.psi (M : Model) (P : ℝ) : ℝ :=
  ∑' n : ℕ, M.β ^ n * (M.C * (M.T^[n]) P)

end RossQC.AlwaysProduce


