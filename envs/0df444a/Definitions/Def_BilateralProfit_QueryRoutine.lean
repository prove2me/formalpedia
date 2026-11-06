-- Prove2me | Definitions.Def_BilateralProfit_QueryRoutine
-- name    : BilateralProfit_QueryRoutine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:32.88018+00:00
-- url     : https://prove2.me/theorems/9ef4100c-1d1f-4200-b535-db262ce1d3d8
-- title:
--   Adaptive query routines and the probability of their output
-- statement:
--   A **query routine** issues queries one at a time; each query is chosen as a function of the observations received so far, and the routine finally outputs an estimate. Each query returns a fresh random observation, independent of all earlier ones; the $n$-th observation of a given query has a prescribed law.
--
--   Formally a routine is a decision tree whose leaves carry outputs and whose internal nodes carry a query and a continuation for every real observation. It **makes at most $N$ queries** if every root-to-leaf path has at most $N$ query nodes, and it **queries only in a set $S$** if every query node on every path lies in $S$. The probability that the output satisfies an event $E$ is the nested integral, over the successive independent observations, of the indicator of $E$ at the leaf reached.
--
--   These are the routines of Lemma 4.8 (pricing queries, observations the trade bit or a variable with the same mean) and the procedures of Claim 4.10 (queries $g(y)$, observations the next unused variable of the sequence $Z^{(1)}_{g,y},Z^{(2)}_{g,y},\dots$).
--
--   **Formalization Note** Routines are deterministic functions of past observations; they never see the law that generates the observations. Query counts and query sets are sure, path-by-path bounds. The probability is a lower Lebesgue integral (in $[0,\infty]$), so a non-measurable routine can only lose probability.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma 4.8, p.24 (PDF 26); Claim 4.10, p.27 (PDF 29) and its proof, App. A.4, pp.57–58 (PDF 59–60); proof of Lemma 4.5, p.29 (PDF 31)

import Mathlib

namespace BilateralProfit

open MeasureTheory

/-! # Adaptive query routines and the law of their output

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), the "routine" of
Lemma 4.8, p.24 (PDF 26), and the "procedure" of Claim 4.10, p.27 (PDF 29): a routine issues
queries one at a time, each choice depending on the observations so far, and finally outputs
estimates. Each query returns a fresh random observation, independent of everything before.

**Formalization Note.** A routine is a decision tree `QTree Q Out`: a leaf `done o` outputs `o`;
a node `query q k` queries `q` and continues with `k r` on observation `r ∈ ℝ`. The routine sees
only past observations (it is a function of them), never the law that generates them.
`QueriesAtMost n` bounds the number of queries on every path, and `AllQueries p` says every query
on every path satisfies `p`; both are sure, path-by-path bounds. The law of the observations is
`obs q n`: the law of the `(n+1)`-th observation of query `q` (Claim 4.10's "next unused
variable in its sequence"); a routine with i.i.d. observations uses `fun q _ => ν q`. `prob`
is the probability that the output satisfies `E`, computed as the nested integral over the
successive independent observations (lower Lebesgue integral, so a non-measurable routine can
only lose probability). `cnt q` is the number of earlier queries of `q`. -/

/-- An adaptive deterministic query routine with queries in `Q` and output in `Out`. -/
inductive QTree (Q : Type) (Out : Type) : Type where
  | done : Out → QTree Q Out
  | query : Q → (ℝ → QTree Q Out) → QTree Q Out

namespace QTree

variable {Q Out : Type}

/-- Every run of the routine makes at most `n` queries. -/
def QueriesAtMost : QTree Q Out → ℕ → Prop
  | done _, _ => True
  | query _ _, 0 => False
  | query _ k, n + 1 => ∀ r, QueriesAtMost (k r) n

/-- Every query the routine can make satisfies `p`. -/
def AllQueries (p : Q → Prop) : QTree Q Out → Prop
  | done _ => True
  | query q k => p q ∧ ∀ r, AllQueries p (k r)

/-- The probability that the output satisfies `E`, when the `(n+1)`-th observation of query `q`
has law `obs q n`, all observations are independent, and `cnt q` queries of `q` have already
been made. -/
noncomputable def prob [DecidableEq Q] (obs : Q → ℕ → Measure ℝ) (E : Out → Prop) :
    QTree Q Out → (Q → ℕ) → ENNReal
  | done o, _ => by classical exact if E o then 1 else 0
  | query q k, cnt =>
      ∫⁻ r, prob obs E (k r) (Function.update cnt q (cnt q + 1)) ∂(obs q (cnt q))

end QTree

end BilateralProfit


