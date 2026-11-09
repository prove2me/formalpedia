-- Prove2me | Definitions.Def_SignFreeOracle_Separation_Trees
-- name    : SignFreeOracle_Separation_Trees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:09.865745+00:00
-- url     : https://prove2.me/theorems/ccb20674-1040-4d97-9e17-eebaca7e6c09
-- title:
--   Integral parameters and actual self-similar trees
-- statement:
--   Write $K=\sqrt n$, $d_{n,k}=2n-kK$, $\ell_{n,k}=10kn\sqrt n\log_2n$, and $m(n)=15n^3\log_2^2n$. Admissible parameters have integral $K$, every required depth, and $m$. The set is unbounded: $n=4^s$, $s\ge1$, is admissible. Natural floors merely make the constructor total; admissibility requires equality with the original real formulas, so they change no admitted dimension.
--
--   A finite tree is represented by an explicit preorder vertex count, parent/child edge list, and distinguished outer-leaf list. A perfect tree of depth $\ell_{n,k}$ with $d_{n,k}-1$ children per internal vertex receives $K$ fresh copies of each previously constructed $\widehat T_{n,j}$, $1\le j<k$, at every internal vertex. Only the leaves of the outer perfect tree are its 0-level leaves. Thus
--   $$\widehat T_{n,1}=C_{n,1},\qquad \widehat T_{n,k}=C_{n,k}\text{ with the specified recursive attachments}.$$
--   The edge lists are actual recursive constructions, not arbitrary trees satisfying a hardness predicate. Integrality corrects the undefined number of children $3-\sqrt2$ at $n=2,k=1$; binary logarithms are the stated reading for the bit-count and entropy conventions.
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Definition 3.6, pp. 10–11 (PDF pp. 10–11)

import Mathlib

set_option autoImplicit false

namespace SignFreeOracle.Separation

/-- A finite rooted tree in preorder, with root 0. Edges are parent/child pairs, and
marked vertices are precisely the distinguished leaves of the outer perfect tree. -/
structure TreeShape where
  size : ℕ
  edges : List (ℕ × ℕ)
  marked : List ℕ
  deriving Inhabited

/-- Disjoint placement of child trees after the root, with an edge to each child root. -/
def placeChildren : ℕ → List TreeShape → List (ℕ × ℕ) × List ℕ
  | _, [] => ([], [])
  | offset, t :: ts =>
    let rest := placeChildren (offset + t.size) ts
    ((0, offset) :: (t.edges.map fun e => (offset + e.1, offset + e.2)) ++ rest.1,
      (t.marked.map (offset + ·)) ++ rest.2)

def treeNode (marked : Bool) (children : List TreeShape) : TreeShape :=
  let placed := placeChildren 1 children
  ⟨1 + (children.map TreeShape.size).sum, placed.1,
    (if marked then [0] else []) ++ placed.2⟩

/-- A perfect tree whose internal vertices each receive the same fresh decoration forest.
Only the leaves of this perfect tree are marked; decoration marks have been erased. -/
def perfectDecorated (branch : ℕ) (attachments : List TreeShape) : ℕ → TreeShape
  | 0 => treeNode true []
  | depth + 1 => treeNode false
      (List.replicate branch (perfectDecorated branch attachments depth) ++ attachments)

noncomputable def logN (n : ℕ) : ℝ := Real.logb 2 n
noncomputable def depth (n k : ℕ) : ℕ :=
  ⌊(k : ℝ) * 10 * n * Real.sqrt n * logN n⌋₊
noncomputable def bits (n : ℕ) : ℕ := ⌊15 * (n : ℝ) ^ 3 * (logN n) ^ 2⌋₊

def degree (n k : ℕ) : ℕ := 2 * n - k * Nat.sqrt n

/-- Admissibility excludes only source formulas that are not integer dimensions.
For example n=4^s, s≥1, is admissible. No restriction of the main theorem is involved. -/
noncomputable def Admissible (n : ℕ) : Prop :=
  1 < n ∧ Nat.sqrt n * Nat.sqrt n = n ∧
  (∀ k, 1 ≤ k → k ≤ Nat.sqrt n →
    (depth n k : ℝ) = (k : ℝ) * 10 * n * Real.sqrt n * logN n) ∧
  (bits n : ℝ) = 15 * (n : ℝ) ^ 3 * (logN n) ^ 2

/-- Recursion in k of Definition 3.6. Copies of every earlier tree are fresh, with
sqrt(n) copies attached to every internal vertex of the new perfect tree. -/
noncomputable def treeList (n : ℕ) : ℕ → List TreeShape
  | 0 => []
  | k + 1 =>
    let previous := treeList n k
    let decorations := previous.flatMap fun t =>
      List.replicate (Nat.sqrt n) {t with marked := []}
    previous ++ [perfectDecorated (degree n (k + 1) - 1) decorations (depth n (k + 1))]

noncomputable def selfSimilar (n k : ℕ) : TreeShape :=
  (treeList n k).getD (k - 1) (treeNode true [])

/-- The forest attached to each base vertex in Definition 3.7. -/
noncomputable def baseForest (n : ℕ) : List TreeShape :=
  (treeList n (Nat.sqrt n - 1)).flatMap fun t => List.replicate (Nat.sqrt n) t

end SignFreeOracle.Separation


