-- Prove2me | Definitions.Def_SFMQueryLower_EmptyMin_OrderedPartition
-- name    : SFMQueryLower_EmptyMin_OrderedPartition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:04.778832+00:00
-- url     : https://prove2.me/theorems/afed76b3-d58e-4960-bbf6-d823a0881246
-- title:
--   Ordered nonempty disjoint blocks and remaining ground sets
-- statement:
--   An ordered partition $\Pi=(P_1,R_1,\ldots,P_k,R_k)$ consists of nonempty, pairwise disjoint blocks covering the $n$-element ground set. Distinctness follows from nonemptiness and disjointness. Define
--   $$V_i=[n]\setminus\bigcup_{j>i}(P_j\cup R_j),\qquad P^\star=\bigcup_{j=1}^kP_j.$$
--   The type of equal partitions additionally takes $n=2k^2$ and $|P_i|=|R_i|=k$. It is used only by Lemma 3.2's uniform sampling. Unequal block sizes remain admissible in the basic partition type and the hard family.
--
--   **Formalization Note** Source layer $j+1$ is stored at index $j$ of `Fin k`; the two Boolean slots hold $P$ and $R$. Subtypes of finite arrays carry only the displayed partition conditions. The equal-partition sample space is nonempty for every positive $k$ by assigning consecutive blocks of $k$ elements.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), partition convention, footnote 9, printed p. 6 / PDF p. 7; Definition 2.2, printed p. 7 / PDF p. 8; Lemma 3.2, printed p. 10 / PDF p. 11

import Mathlib

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin

/-- Source layer `j+1` has blocks `B j false = P_{j+1}`, `B j true = R_{j+1}`.
All blocks are nonempty, pairwise disjoint and cover the ground set. These conditions
also imply distinctness. There is no equal-size condition here. -/
def IsOrderedPartition {n k : ℕ} (B : Fin k → Bool → Finset (Fin n)) : Prop :=
  (∀ j b, (B j b).Nonempty) ∧
  (∀ a c : Fin k × Bool, a ≠ c → Disjoint (B a.1 a.2) (B c.1 c.2)) ∧
  (∀ x : Fin n, ∃ j b, x ∈ B j b)

def OrderedPartition (n k : ℕ) :=
  {B : Fin k → Bool → Finset (Fin n) // IsOrderedPartition B}

noncomputable instance (n k : ℕ) : Fintype (OrderedPartition n k) :=
  by
  classical
  unfold OrderedPartition
  infer_instance

def goodBlock {n k : ℕ} (π : OrderedPartition n k) (j : Fin k) : Finset (Fin n) :=
  π.val j false

def badBlock {n k : ℕ} (π : OrderedPartition n k) (j : Fin k) : Finset (Fin n) :=
  π.val j true

/-- `V_i`: remove the layers with source index greater than `i`. -/
def remainingGround {n k : ℕ} (π : OrderedPartition n k) (i : ℕ) : Finset (Fin n) :=
  Finset.univ \ Finset.univ.biUnion (fun j : Fin k =>
    if i ≤ j.val then goodBlock π j ∪ badBlock π j else ∅)

def distinguishedSet {n k : ℕ} (π : OrderedPartition n k) : Finset (Fin n) :=
  Finset.univ.biUnion (goodBlock π)

/-- Equal sizes are imposed only for the sampling in Lemma 3.2. -/
def EqualPartition (k : ℕ) :=
  {π : OrderedPartition (2 * k ^ 2) k //
    ∀ j : Fin k, (goodBlock π j).card = k ∧ (badBlock π j).card = k}

noncomputable instance (k : ℕ) : Fintype (EqualPartition k) := by
  classical
  unfold EqualPartition
  infer_instance

end SFMQueryLower.EmptyMin


