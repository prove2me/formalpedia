-- Prove2me | Definitions.Def_CommitteeVoting_ExpConv_Supplement_RandomTypes
-- name    : CommitteeVoting_ExpConv_Supplement_RandomTypes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:20:12.350878+00:00
-- url     : https://prove2.me/theorems/70da4511-091c-42e9-84a0-6211e4292e8a
-- title:
--   Theorem 2, pp. 16, 42 — random types, conditional score law and honest-committee success
-- statement:
--   There are $m$ producers and $n$ voters. Let $p\in[0,1]$, and let $f^h$ and $f^m$ be probability mass functions on $\{0,\ldots,n\}$, the vote counts of honest and dishonest producers. Types are independent, each producer honest with probability $p$. Given the honest set $A$, the vote counts $s_j$ are independent, with law $f^h$ for $j\in A$ and $f^m$ otherwise. The joint mass is
--
--   $$w(A,s)=p^{|A|}(1-p)^{m-|A|}\prod_{j\in A}f^h(s_j)\prod_{j\notin A}f^m(s_j).$$
--
--   For a committee size $k\le m$, the success probability is
--
--   $$S(m,k,p,f^h,f^m)=\sum_{A\subseteq\{1,\ldots,m\}}\sum_{s\in\{0,\ldots,n\}^m}w(A,s)\,\mathbf1\!\left[\text{every admissible }T\text{ has }|T\cap A|\ge\lceil(1-p)k\rceil\right].$$
--
--   Here $T$ is admissible precisely when it has $k$ members and no outsider scores above a member. This reuses the published event of Definition 3, including adversarial ties and zero-score filling, without defining success through the formula it is meant to equal.
--
--   **Formalization Note** Generic distributions use Mathlib's `PMF`, with carrier `Fin (n+1)`; their finite masses cannot be infinite. Candidates are indexed by `Fin m`, so paper index $j$ is Lean index $j-1$. The one pair of type-specific laws implements Remark 1. Independence is encoded by the joint product law rather than additional hypotheses. No Gaussian signal model or Poisson-binomial specialization is imposed.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, pp. 14, 16, 42–43, Remark 1; Theorem 2 and its proof; Definition 3, pp. 10–11

import Mathlib
import Definitions.Def_CommitteeVoting_ExpConv_Committee

namespace CommitteeVoting.ExpConv.Supplement

/-- Theorem 2's type-conditional score law. A generic discrete distribution is Mathlib's
`PMF`; `Fin (n+1)` gives precisely scores 0,...,n. Types are iid Bernoulli(p),
and conditional on the honest set all score coordinates are independent. -/
noncomputable def jointWeight {m n : ℕ} (p : ℝ)
    (fh fm : PMF (Fin (n + 1))) (Hon : Finset (Fin m))
    (s : Fin m → Fin (n + 1)) : ℝ :=
  p ^ Hon.card * (1 - p) ^ (m - Hon.card) *
    ∏ j : Fin m, if j ∈ Hon then (fh (s j)).toReal else (fm (s j)).toReal

/-- Success is the published adversarial event, averaged over every type and score vector.
The success event is defined independently of the formula in (12). -/
noncomputable def successProbability {m n : ℕ} (k : ℕ) (p : ℝ)
    (fh fm : PMF (Fin (n + 1))) : ℝ := by
  classical
  exact ∑ Hon : Finset (Fin m), ∑ s : Fin m → Fin (n + 1),
    if CommitteeVoting.ExpConv.IsHonestOutcome k p Hon (fun j => (s j : ℕ))
    then jointWeight p fh fm Hon s else 0

end CommitteeVoting.ExpConv.Supplement


