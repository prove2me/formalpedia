-- Prove2me | Definitions.Def_SunflowerIndexedSpread
-- name    : SunflowerIndexedSpread
-- status  : Definition
-- author  : @lunjia
-- created : 2026-09-26T17:14:08.389955+00:00
-- url     : https://prove2.me/theorems/0b6e6dbc-f290-47d2-9a29-0625eb712670
-- title:
--   Normalized spread for indexed finite families
-- statement:
--   For a finite set of labels $I$ and an indexed family $(A_i)_{i\in I}$ of finite subsets of a ground type, normalized $R$-spread means
--
--   $$R^{|T|}\,|\{i\in I:T\subseteq A_i\}|\le |I|\qquad\text{for every finite }T.$$
--
--   Labels are counted separately, even when their members coincide. Empty members are permitted. This convention supports iterated refinement, where residual sets may become equal while their original labels remain distinct. The predicate itself imposes no sign assumption on $R$ or nonemptiness assumption on $I$; theorems state the conditions they require.
-- source:
--   L. Hu, Entropy Estimation via Two Chains (19 May 2021), Definition 1 and Lemma 2, https://theorydish.blog/2021/05/19/entropy-estimation-via-two-chains-streamlining-the-proof-of-the-sunflower-lemma/ ; T. Tao, The sunflower lemma via Shannon entropy (20 July 2020), Definition 1 and refinement argument, https://terrytao.wordpress.com/2020/07/20/the-sunflower-lemma-via-shannon-entropy/ . This is an indexed, normalized-spread Bernoulli adaptation of those arguments, not a verbatim restatement of the fixed-cardinality sampling lemma.

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace Erdos20

/-- Spread for a uniformly sampled indexed family. Repeated members retain
their labels, so every cardinality here counts multiplicity. -/
def IndexedSpread {α ι : Type*} [DecidableEq α] [Fintype ι]
    (R : ℝ) (A : ι → Finset α) : Prop :=
  ∀ T : Finset α,
    R ^ T.card * ((Finset.univ.filter (fun i => T ⊆ A i)).card : ℝ) ≤
      Fintype.card ι

end Erdos20


