-- Prove2me | Definitions.Def_GraphIsoTesting_FixedGraph_BinarySystems
-- name    : GraphIsoTesting_FixedGraph_BinarySystems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:30:42.303994+00:00
-- url     : https://prove2.me/theorems/8517a82c-785e-4abd-8c09-1f7c6bfef2b6
-- title:
--   Binary linear images, Hamming distance, sparse weights, and coordinate testers
-- statement:
--   For natural numbers $m,k$, a binary matrix $A$ has $m$ rows and $k$ columns over $\mathbb F_2$. Its image consists of all vectors $Ax$ for $x\in\mathbb F_2^k$. Define
--
--   $$D_A(b)=\min_{x\in\mathbb F_2^k}|\{j:(Ax)_j\ne b_j\}|.$$
--
--   The minimum ranges over a nonempty finite set, including when $k=0$. Independence up to a real threshold $t$ means that every set $S$ of rows with $|S|\le t$ is linearly independent over $\mathbb F_2$. The empty row family is included. The sparse-weight predicate requires every row to contain exactly three nonzero entries and every column exactly six.
--
--   A coordinate tester accesses $b$ only by queries to its coordinates. It accepts every $b\in\operatorname{Im}(A)$ and rejects every $b$ with $D_A(b)>\beta m$, each with probability at least $2/3$. The matrix is fixed and known and need not have full column rank. These definitions separate general image-membership testing from the later sparse construction.
--
--   **Formalization Note** Bits are `ZMod 2`; $m$ replaces the paper's equation-count symbol $n$.
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), pp. 4–5, §2 distance, Claim 2.1, Theorem 2.2 and Lemma 2.3

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_QueryModel

namespace GraphIsoTesting.FixedGraph

abbrev Bit := ZMod 2
abbrev BinaryMatrix (m k : ℕ) := Matrix (Fin m) (Fin k) Bit

def matrixImage {m k : ℕ} (A : BinaryMatrix m k) : Set (Fin m → Bit) :=
  Set.range A.mulVec

noncomputable def hammingDistance {m : ℕ} (a b : Fin m → Bit) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => a j ≠ b j).card

/-- A finite attained minimum over all x, including the zero vector when k = 0. -/
noncomputable def imageDistance {m k : ℕ} (A : BinaryMatrix m k)
    (b : Fin m → Bit) : ℕ := by
  classical
  exact Finset.univ.inf' Finset.univ_nonempty (fun x => hammingDistance (A.mulVec x) b)

/-- The real threshold includes the empty row family; no rounding or rank assumption. -/
def IndependentRowsUpTo {m k : ℕ} (A : BinaryMatrix m k) (t : ℝ) : Prop :=
  ∀ S : Finset (Fin m), (S.card : ℝ) ≤ t →
    LinearIndependent Bit (fun j : S => A j.val)

noncomputable def Sparse36 {m k : ℕ} (A : BinaryMatrix m k) : Prop := by
  classical
  exact (∀ j, (Finset.univ.filter fun i => A j i ≠ 0).card = 3) ∧
    (∀ i, (Finset.univ.filter fun j => A j i ≠ 0).card = 6)

noncomputable def IsImageTester {m k q : ℕ} (A : BinaryMatrix m k) (β : ℝ)
    (T : RandomizedTester (Fin m) Bit q) : Prop :=
  ∀ b : Fin m → Bit,
    (b ∈ matrixImage A → (2 / 3 : ENNReal) ≤ outputProbability T b true) ∧
    (β * (m : ℝ) < (imageDistance A b : ℝ) →
      (2 / 3 : ENNReal) ≤ outputProbability T b false)

end GraphIsoTesting.FixedGraph


