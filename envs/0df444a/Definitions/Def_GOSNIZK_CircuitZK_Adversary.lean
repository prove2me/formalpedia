-- Prove2me | Definitions.Def_GOSNIZK_CircuitZK_Adversary
-- name    : GOSNIZK_CircuitZK_Adversary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:23:41.647978+00:00
-- url     : https://prove2.me/theorems/91b90d7f-a676-4a8d-b72b-263bdfffb588
-- title:
--   Adaptive randomized oracle adversaries as query trees, and their output law
-- statement:
--   An **adaptive oracle adversary** with queries in $Q$ and answers in $A$ is a well-founded tree with three kinds of nodes: a leaf that halts with an output bit $b$; a coin node that tosses a fair coin and continues in one of two subtrees; and a query node that sends a query $q \in Q$ to the oracle, receives an answer $a \in A$ and continues in the subtree for $a$.
--
--   Given a randomized oracle $O$, which answers each query $q$ with a sample of the distribution $O(q)$, independently of all earlier queries, the adversary's **output law** $A^{O}$ is the distribution of the bit at the leaf it reaches:
--   $$A^{O} = \begin{cases} \delta_b & \text{at a leaf } b,\\ \tfrac12 A_0^{O} + \tfrac12 A_1^{O} & \text{at a coin node},\\ \sum_a O(q)(a)\, A_a^{O} & \text{at a query node } q.\end{cases}$$
--
--   This is the oracle-access model $A^{P(\sigma,\cdot,\cdot)}$ of the paper's definition of zero-knowledge: the adversary sees only the oracle's input-output behaviour and chooses each query after seeing the earlier answers.
--
--   **Formalization Note** Every adversary that halts after finitely many steps on every run, in particular every polynomial-time one with any non-uniform advice, is such a tree; quantifying over all trees is stronger than quantifying over polynomial-time adversaries. The fair coin is the adversary's only source of randomness.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 5, Section 2 and footnote 6 (oracle access)

import Mathlib

namespace GOSNIZK.CircuitZK

/-- An adaptive, randomized oracle adversary with queries in `Q` and answers in `A`, as a well-founded tree:
`ret b` halts with output `b`; `flip k` tosses a fair coin `b` and continues as `k b`; `query q k` asks the oracle
`q`, receives an answer `a` and continues as `k a`. Every adversary that halts after finitely many steps on each
run, in particular every polynomial-time one, is such a tree; non-uniform advice is part of the tree. -/
inductive Adv (Q A : Type) : Type where
  | ret : Bool → Adv Q A
  | flip : (Bool → Adv Q A) → Adv Q A
  | query : Q → (A → Adv Q A) → Adv Q A

/-- The output distribution of the adversary run with oracle access to the randomized oracle `O`: each query is
answered by a fresh, independent sample of `O q`. -/
noncomputable def Adv.run {Q A : Type} (O : Q → PMF A) : Adv Q A → PMF Bool
  | .ret b => PMF.pure b
  | .flip k => (PMF.uniformOfFintype Bool).bind fun b => (k b).run O
  | .query q k => (O q).bind fun a => (k a).run O

end GOSNIZK.CircuitZK


