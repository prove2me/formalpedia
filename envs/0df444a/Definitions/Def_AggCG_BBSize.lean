-- Prove2me | Definitions.Def_AggCG_BBSize
-- name    : AggCG_BBSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:07:08.621242+00:00
-- url     : https://prove2.me/theorems/16be9fe0-8902-4c67-8eb7-2d11f3c27495
-- title:
--   The branch-and-bound tree size $\mathrm{TreeSize}_u(I)$
-- statement:
--   Fix a program $I$ and a root cut. A run of LP-based **branch and bound** from a node with branching bounds $B$ generates $k$ nodes, written $\mathrm{BBSize}(B,k)$, in one of three ways:
--
--   1. the node LP is infeasible, and $k=1$;
--   2. the node LP has an integral optimum, and $k=1$;
--   3. the node LP has an optimum $z$ with $z_j\notin\mathbb Z$, the children with the added bounds $z_j\le\lfloor z_j\rfloor$ and $z_j\ge\lceil z_j\rceil$ have sizes $k_1,k_2$, and $k=1+k_1+k_2$.
--
--   Then
--   $$\mathrm{TreeSize}_u(I)=\min\{k:\mathrm{BBSize}([\,],k)\text{ with the cut (19) at the root}\}.$$
--   The solver applies only this root cut, with no presolve and no further cuts, and it counts all generated nodes including the root.
--
--   **Formalization Note** The paper names no LP solver, branching rule or node order, so a run may use every LP optimum and every fractional variable. There is no pruning by bound: on the gadgets the optimum is unique and both children are leaves, so none could remove a generated node. Lemma I.1 proves that all runs on a gadget have one size, which is 1 or 3. The size is computed from this tree, never from the closed form of Lemma I.1.
-- source:
--   Sharma, Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms, STOC 2027 submission (manuscript sha256 f7ea0248…), §I, p.49 (PDF p.50)

import Mathlib
import Definitions.Def_AggCG_IP

namespace AggCG

/-- The B&B tree of an LP-based branch and bound with a fixed root cut, as a relation: `BBSize I cut B k` says
that some run from the node with branching bounds `B` generates `k` nodes, the node included (Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), §I, p.49, PDF p.50: the solver
"applies only this root cut, disables preprocessing and additional separation, and counts all generated nodes including the root").

**Formalization Note** The paper names no LP solver, branching rule or node order, so every LP optimum and every
fractional variable is allowed. A node is a leaf if its LP is infeasible or has an integral optimum; otherwise it branches on a
fractional `z_j` into `z_j ≤ ⌊z_j⌋` and `z_j ≥ ⌈z_j⌉`. There is no pruning by bound: on the gadgets the optimum is unique and both children are leaves, so
none could remove a generated node (`lemma_I_1`). A node whose LP has no optimum has no size. -/
inductive BBSize {m n : ℕ} (I : IP m n) (cut : IntCut n) : List (BranchCon n) → ℕ → Prop
  | infeasible (B : List (BranchCon n)) : I.nodeRegion (some cut) B = ∅ → BBSize I cut B 1
  | integral (B : List (BranchCon n)) (z : Fin n → ℝ) :
      I.IsLPOpt (some cut) B z → IsIntegralPt z → BBSize I cut B 1
  | branch (B : List (BranchCon n)) (z : Fin n → ℝ) (j : Fin n) (k₁ k₂ : ℕ) :
      I.IsLPOpt (some cut) B z → (¬ ∃ k : ℤ, z j = k) →
      BBSize I cut (BranchCon.le j ⌊z j⌋ :: B) k₁ →
      BBSize I cut (BranchCon.ge j ⌈z j⌉ :: B) k₂ →
      BBSize I cut B (1 + k₁ + k₂)

/-- `TreeSize_u(I)`, p.49: the number of B&B nodes after adding the cut (19).

**Formalization Note** The least size of a run. `lemma_I_1` proves that on every gadget all runs have one size, so nothing is
chosen there; the closed form of Lemma I.1 is a theorem, not this definition. -/
noncomputable def treeSize {m n : ℕ} (I : IP m n) (u : Fin m → ℝ) : ℕ :=
  sInf {k | BBSize I (I.cutOf u) [] k}

end AggCG


