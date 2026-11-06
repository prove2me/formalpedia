-- Prove2me | Definitions.Def_BorelRobustMDP_MarkovPolicy
-- name    : BorelRobustMDP_MarkovPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:07.533354+00:00
-- url     : https://prove2.me/theorems/31d46434-27ee-4eeb-b5bc-4c5bb445f165
-- title:
--   Deterministic Markov policies $\Pi^M$ and the inclusion $\Pi^M\subseteq\Pi^R$
-- statement:
--   A **Markov decision rule** at time $n$ is a measurable $d:E\to A$ with $d(x)\in D_n(x)$ for all $x$. A **Markov policy** is a sequence $\pi=(d_0,\dots,d_{N-1})$ of such rules. It is a randomized policy through the Dirac kernels $\pi_n(\cdot\mid h_n)=\delta_{d_n(x_n)}$.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, Definition 2.2 (ii)–(iii), p.3

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_DecisionModel
import Definitions.Def_BorelRobustMDP_Feasible
import Definitions.Def_BorelRobustMDP_Policy

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (Hist histState measurable_histState)

namespace BorelRobustMDP

universe u v

variable {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A] [MeasurableSpace Z]
  {N : ℕ}

/-- A Markov decision rule at time `n` (Bäuerle & Glauner, arXiv:2007.13103v1, Definition 2.2 (ii),
(iii), p.3): a measurable map `d : E → A` with `d(x) ∈ D_n(x)`. -/
def IsDecisionRule (M : DecisionModel E A Z N) (n : ℕ) (d : E → A) : Prop :=
  Measurable d ∧ ∀ x, (x, d x) ∈ M.D n

/-- A deterministic Markov policy `π = (d_0, …, d_{N−1}) ∈ Π^M` (Bäuerle & Glauner,
arXiv:2007.13103v1, Definition 2.2 (iii), p.3). -/
structure MarkovPolicy (M : DecisionModel E A Z N) where
  rule : Fin N → E → A
  isDecisionRule : ∀ n : Fin N, IsDecisionRule M n (rule n)

/-- The inclusion `Π^M ⊆ Π^R` (Bäuerle & Glauner, arXiv:2007.13103v1, p.3): the decision rule `d_n`
is identified with the Dirac kernels `π_n(· | h_n) = δ_{d_n(x_n)}`. -/
noncomputable def MarkovPolicy.toPolicy {M : DecisionModel E A Z N} (d : MarkovPolicy M) :
    Policy M where
  kernel n := Kernel.deterministic (fun h : Hist E A n => d.rule n (histState n h))
    ((d.isDecisionRule n).1.comp (measurable_histState n))
  isMarkovKernel n := inferInstance
  constraint n h _ := by
    have hs : MeasurableSet (M.sec n (histState n h)) :=
      measurable_prodMk_left (M.measurableSet_D n n.2)
    rw [Kernel.deterministic_apply, Measure.dirac_apply' _ hs,
      Set.indicator_of_mem
        (show d.rule n (histState n h) ∈ M.sec n (histState n h) from (d.isDecisionRule n).2 _)]
    rfl

/-- The law of the action at time `k` in state `x`: the Dirac measure at `d_k(x)`, `0` beyond the
horizon, where it is never used. -/
noncomputable def MarkovPolicy.act {M : DecisionModel E A Z N} (d : MarkovPolicy M) (k : ℕ)
    (x : E) : Measure A :=
  if hk : k < N then Measure.dirac (d.rule ⟨k, hk⟩ x) else 0

end BorelRobustMDP


