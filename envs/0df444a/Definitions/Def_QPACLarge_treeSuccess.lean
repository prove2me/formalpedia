-- Prove2me | Definitions.Def_QPACLarge_treeSuccess
-- name    : QPACLarge_treeSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:16.388508+00:00
-- url     : https://prove2.me/theorems/4c0cbd4f-b90a-4627-8251-9842368c2aa6
-- title:
--   Success probability of a randomized membership-query learner
-- statement:
--   A randomized classical learner with membership queries chooses points $y \in \{0,1\}^n$ adaptively, receives $f(y)$, and outputs a hypothesis $h$. With its coins fixed it is a decision tree: an internal node queries a point and branches on the answer, a leaf holds the hypothesis. A randomized learner is a probability distribution $R$ over such trees, and its success probability for a property $P$ of hypotheses on the target $f$ is
--
--   $$
--   \Pr_{t \sim R}\big[P(h_t(f))\big],
--   $$
--
--   where $h_t(f)$ is the hypothesis at the leaf that $f$'s answers lead to.
--
--   **Formalization Note** The trees are the published `QAlgorithms.RandDecisionTree` (a `PMF` over `DecisionTree`); leaves carry hypotheses as functions, so a learner that outputs a circuit is the tree whose leaves carry the functions computed. The number of queries is bounded with the published `RandMakesAtMost`.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.2, p.15 (Membership Queries); Theorem 4.1, p.30; Lemma 5.1, p.34

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical

namespace QPACLarge

open QAlgorithms

/-- **Success probability of a randomized membership-query learner.**
Oliveira, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.2, p.15 ("Membership Queries")
and Theorem 4.1 / Lemma 5.1, pp.30, 34: a randomized classical learner with membership access to
`f` queries points `y ∈ {0,1}ⁿ`, receives `f(y)`, and outputs a hypothesis `h`.

`treeSuccess R f P` is the probability, over the learner's randomness, that the hypothesis output
on target `f` satisfies `P`. The learner is a published randomized decision tree
(`QAlgorithms.RandDecisionTree`, a probability distribution over deterministic adaptive query
trees): a node queries `f` at a point and branches on the answer, a leaf outputs the hypothesis.

**Formalization Note.** Leaves carry the hypothesis as a function `{0,1}ⁿ → {0,1}`; a learner
that outputs a circuit `h` is the tree whose leaves carry the function `h` computes. -/
noncomputable def treeSuccess {n : ℕ} (R : RandDecisionTree (Qubits n) Bool (Qubits n → Bool))
    (f : Qubits n → Bool) (P : (Qubits n → Bool) → Prop) : ℝ :=
  (R.toOuterMeasure {t | P (t.eval f)}).toReal

end QPACLarge


