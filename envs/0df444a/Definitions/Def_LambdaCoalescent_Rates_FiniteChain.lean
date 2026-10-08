-- Prove2me | Definitions.Def_LambdaCoalescent_Rates_FiniteChain
-- name    : LambdaCoalescent_Rates_FiniteChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:33.363663+00:00
-- url     : https://prove2.me/theorems/753a4432-069f-4757-a8ab-8a6810566f85
-- title:
--   Finite-state continuous-time Markov chain specified by generator Q
-- statement:
--   Let $S$ be a finite measurable state space, $Q$ a real matrix indexed by $S$, $s_0\in S$, and $P$ a measure governing a state-valued process $X(t)$. The process has the **rate-chain law** for $Q$ from $s_0$ when every $X(t)$ is measurable and, for every finite ordered list $0=t_0\le\cdots\le t_k$ and listed states $a_0,\ldots,a_k$,
--
--   $$
--   P(X(t_0)=a_0,\ldots,X(t_k)=a_k)
--   =\prod_{i=0}^{k-1}\bigl[\exp((t_{i+1}-t_i)Q)\bigr]_{a_i,a_{i+1}},
--   $$
--
--   with probability zero when $a_0\ne s_0$. The finite-dimensional law fixes the Markov transition behavior used in the coalescent setting.
--
--   **Formalization Note** Time is nonnegative real. This definition records the law and measurability; theorem statements separately require $P$ to be a probability measure and $Q$ to be the generator built from nonnegative merger rates.
-- source:
--   Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), p. 1882, §3.1, finite Markov chains and transition rates

import Mathlib

namespace LambdaCoalescent.Rates

open MeasureTheory
open scoped BigOperators NNReal

/-- Finite-dimensional distributions of a continuous-time finite-state chain with generator `Q`. -/
def IsRateChain {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    [Fintype S] [DecidableEq S] (P : Measure Ω) (Q : Matrix S S ℝ) (s₀ : S)
    (X : ℝ≥0 → Ω → S) : Prop :=
  (∀ t, Measurable (X t)) ∧
  ∀ (k : ℕ) (t : Fin (k + 1) → ℝ≥0), t 0 = 0 → Monotone t →
    ∀ s : Fin (k + 1) → S,
      P.real {ω | ∀ i, X (t i) ω = s i} =
        (if s 0 = s₀ then 1 else 0) *
          ∏ i : Fin k,
            NormedSpace.exp (((t i.succ : ℝ) - (t i.castSucc : ℝ)) • Q)
              (s i.castSucc) (s i.succ)

end LambdaCoalescent.Rates


