-- Prove2me | Definitions.Def_DilatableEntropy_SeqDecisionProblem
-- name    : DilatableEntropy_SeqDecisionProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:12.610545+00:00
-- url     : https://prove2.me/theorems/b77bf0e2-dac1-4697-953e-4052deebc71b
-- title:
--   Sequential decision problem (tree of decision points) and its set of sequences $\Sigma$
-- statement:
--   A **sequential decision problem** of one player consists of
--
--   1. a finite set $J$ of **decision points**;
--   2. at each $j\in J$ a finite, nonempty set $A_j$ of **actions**, with $|A_j|=n_j$;
--   3. for each $j\in J$ a **parent sequence** $p_j$: the last decision point–action pair $ja$ on the path from the root to $j$, or the **empty sequence** $\varnothing$ if the player does not act before $j$.
--
--   The decision points form a tree: the relation "$j'$ is a child of $j$", i.e. $p_{j'}=ja$ for some $a\in A_j$, is well-founded. There may be several root decision points and $J$ may be empty. The set of **sequences** is
--   $$
--   \Sigma:=\{\varnothing\}\cup\{ja : j\in J,\ a\in A_j\}.
--   $$
--   For an extensive-form game with perfect recall, the decision points of a player are its information sets.
--
--   This is the domain of every object of the mission: sequence-form strategies are vectors indexed by $\Sigma$.
--
--   **Formalization Note** `parent : J → Option (Σ j, A j)` with `none` for $\varnothing$; `Seq P := Option (Σ j, P.A j)`. Because each decision point has exactly one parent sequence, the sets $\mathcal C_{ja}=\{j' : p_{j'}=ja\}$ are pairwise disjoint, which is the paper's tree assumption.
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, §4, pp.7–8 (decision points, actions, parent sequence p_j, sequences Σ)

import Mathlib

namespace DilatableEntropy

/-- A **sequential decision problem** (tree-form decision process) of one player
(Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, §4, pp.7–8): a finite set `J` of decision points; at each decision point `j` a finite,
nonempty set of actions `A j` (`|A_j| = n_j`); and for each `j` its *parent sequence*
`p_j = parent j`, the last decision point–action pair on the path from the root to `j`
(`none` is the empty sequence `∅`, used when the player does not act before `j`).
The decision points form a tree: the relation "`j'` is a child of `j`", i.e.
`∃ a, p_{j'} = ja`, is well-founded. There may be several root decision points
(`p_j = ∅`), and `J` may be empty.

**Formalization Note** The sets `C_{ja} = {j' : p_{j'} = ja}` are pairwise disjoint because
each decision point has exactly one parent sequence (the paper's tree assumption,
`C_{ja} ∩ C_{j'a'} = ∅`); well-foundedness of the child relation is "the decision points form a
tree" for a finite `J`. Action sets are nonempty: a strategy assigns a probability
distribution over `A_j` at every decision point (p.7), and `log |A_j|` (Definition 4) needs
`|A_j| ≥ 1`. -/
structure SeqDecisionProblem where
  /-- The decision points `J`. -/
  J : Type
  [instFintypeJ : Fintype J]
  [instDecEqJ : DecidableEq J]
  /-- The action set `A_j` at decision point `j`. -/
  A : J → Type
  [instFintypeA : ∀ j, Fintype (A j)]
  [instDecEqA : ∀ j, DecidableEq (A j)]
  [instNonemptyA : ∀ j, Nonempty (A j)]
  /-- The parent sequence `p_j` of decision point `j` (`none` = the empty sequence `∅`). -/
  parent : J → Option (Σ j, A j)
  /-- The decision points form a tree: the child relation is well-founded. -/
  wf : WellFounded (fun j' j => ∃ a, parent j' = some ⟨j, a⟩)

attribute [instance] SeqDecisionProblem.instFintypeJ SeqDecisionProblem.instDecEqJ
  SeqDecisionProblem.instFintypeA SeqDecisionProblem.instDecEqA
  SeqDecisionProblem.instNonemptyA

/-- The set of **sequences** `Σ := {∅} ∪ {ja : j ∈ J, a ∈ A_j}` of a sequential decision problem
(Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, §4, p.7). `none` is the empty sequence `∅` and `some ⟨j, a⟩` is the sequence `ja`.
A sequence-form vector is a function `Seq P → ℝ`, i.e. a point of `ℝ^{|Σ|}`. -/
abbrev Seq (P : SeqDecisionProblem) : Type := Option (Σ j, P.A j)

end DilatableEntropy


