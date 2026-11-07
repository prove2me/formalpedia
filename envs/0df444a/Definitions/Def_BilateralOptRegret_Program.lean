-- Prove2me | Definitions.Def_BilateralOptRegret_Program
-- name    : BilateralOptRegret_Program
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:30.559532+00:00
-- url     : https://prove2.me/theorems/4f0a9208-43c6-4ded-a854-92380c172691
-- title:
--   Adaptive programs: sequencing, the list of queries, and the policy of a program
-- statement:
--   The procedures of the paper issue one-bit queries adaptively, and are modelled as decision trees whose nodes are queries and whose branches are the observations. This item adds to the published `BilateralProfit.QTree`: sequencing of programs; the **traced** program, whose output also lists its queries in order; the **probability of an event** on (output, list of queries) under the observations of $L$; the predicate that a property holds at every leaf of a program; and the **policy** of a program, which follows the tree along the trade bits and, at a leaf, keeps playing the leaf's action.
--
--   An event on the output and the query list together is what expresses the paper's guarantees "on the same event": accuracy, number of observations, and suboptimality of the queries.
--
--   **Formalization Note** A program sees only its observations: it cannot read $L$, $F$, $\mathrm{OPT}$ or $\mathrm{gap}$. "Stop if the horizon is exhausted" is automatic, as only rounds $t<T$ enter the regret.
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Definition 4.1, p.15; Algorithms 1, 3, 4

import Mathlib
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model

namespace BilateralOptRegret

open BilateralProfit

/-! # Programs: sequencing, the trace of queries, and the policy of a program

Castiglioni, Lunghi, Marchesi (manuscript, sha256 aafed174…): the procedures Refine (Definition 4.1,
p.15) and Algorithms 1, 3, 4 issue one-bit queries adaptively.

**Formalization Note.** A procedure is a `BilateralProfit.QTree` over grid actions: it sees only its
observations, never `L`, `F`, `OPT` or `gap`. `traced t` runs `t` and also outputs the list of queries
made, so the accuracy, the observation count and the gaps of the queries can be stated **on one event**
(`succProb`). `Sure p t` says `p` holds at every leaf of `t`, for every sequence of observations.
`policyOf` turns a program into a policy on trade bits: it follows the tree along the bits, and at a
leaf `done o` it keeps playing `o` (commitment). "Stop if the horizon is exhausted" (Algorithm 1) is
automatic: only rounds `t < T` enter the regret. -/

/-- Run a program, then continue with a program depending on its output. -/
def qBind {Q A B : Type} : QTree Q A → (A → QTree Q B) → QTree Q B
  | .done a, f => f a
  | .query q k, f => .query q (fun o => qBind (k o) f)

instance (Q : Type) : Monad (QTree Q) where
  pure := .done
  bind := qBind

/-- The program `t`, with output paired with the list of the queries it made, in order. -/
def traced {Q Out : Type} : QTree Q Out → QTree Q (Out × List Q)
  | .done o => .done (o, [])
  | .query q k => .query q (fun o => qBind (traced (k o)) (fun p => .done (p.1, q :: p.2)))

/-- `p` holds at every leaf, for every sequence of observations. -/
def Sure {Q Out : Type} (p : Out → Prop) : QTree Q Out → Prop
  | .done o => p o
  | .query _ k => ∀ o, Sure p (k o)

/-- The probability, under the observations of `L`, that the output of `t` and its list of queries
satisfy `E`. -/
noncomputable def succProb {Out : Type} (L : MeasureTheory.Measure (ℝ × ℝ)) (K : ℕ)
    (t : QTree (Grid K) Out) (E : Out × List (Grid K) → Prop) : ENNReal :=
  QTree.prob (obsLaw L K) E (traced t) (fun _ => 0)

/-- The grid action a program plays next after the given trade bits; at a leaf it commits to the
leaf's action. Trade is the observation `1`, no trade the observation `0`. -/
def nextAct {Q : Type} : QTree Q Q → List Bool → Q
  | .done o, _ => o
  | .query q _, [] => q
  | .query _ k, b :: bs => nextAct (k (if b then 1 else 0)) bs

/-- The policy on trade bits of a program whose output is the action to commit to. -/
noncomputable def policyOf (K : ℕ) (t : QTree (Grid K) (Grid K)) : List Bool → ℝ × ℝ :=
  fun bits => pt K (nextAct t bits)

end BilateralOptRegret


