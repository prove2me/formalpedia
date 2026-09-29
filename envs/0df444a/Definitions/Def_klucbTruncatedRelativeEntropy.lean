-- Prove2me | Definitions.Def_klucbTruncatedRelativeEntropy
-- name    : klucbTruncatedRelativeEntropy
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-07-29T04:01:24.052257+00:00
-- url     : https://prove2.me/theorems/a9981db9-0cc8-441e-bdd9-3d4b4cadb356
-- title:
--   One-sided Bernoulli relative entropy
-- statement:
--   For Bernoulli parameters \(p,q\), define the one-sided, or truncated, relative entropy by
--
--   $$
--   \bar d(p,q)=
--   \begin{cases}
--   d(p,q),&p\le q,\\
--   0,&p>q,
--   \end{cases}
--   $$
--
--   where \(d(p,q)\) is the relative entropy between Bernoulli distributions with means \(p\) and \(q\).
--
--   This is the divergence used in the KL-UCB analysis to express whether an upper confidence threshold \(q\) remains feasible. It makes the one-sided nature of an upper-confidence index explicit and is reused in the optimal-arm underestimation and suboptimal-arm overshoot counts.
--
--   **Formalization Note** The definition is real-valued and inherits the endpoint convention of `bernoulliRelativeEntropy`.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Chapter 10, immediately before Lemma 10.7, printed p. 138 / PDF p. 147: d-bar(p,q)=d(p,q) I{p <= q}.

import Definitions.Def_bernoulliRelativeEntropy

/-!
Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), immediately before
Lemma 10.7, printed p. 138.
-/

namespace BanditAlgorithm

/-- The one-sided binary divergence used in Lemmas 10.7 and 10.8:
`d⁺(p,q) = d(p,q) 𝟙{p ≤ q}`. -/
noncomputable def klucbTruncatedRelativeEntropy (p q : ℝ) : ℝ :=
  if p ≤ q then bernoulliRelativeEntropy p q else 0

end BanditAlgorithm


