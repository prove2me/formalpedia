-- Prove2me | Definitions.Def_HuffmanMPC_Main_Reconstruction
-- name    : HuffmanMPC_Main_Reconstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:14.262409+00:00
-- url     : https://prove2.me/theorems/885eb7ff-2cfe-47cd-810e-7d88e2d7e246
-- title:
--   §6 — labelled coding trees, node weights at depth $h^*$, $P(r)$ and the fractional greedy
-- statement:
--   A coding tree is a finite full binary tree whose leaves carry the indices of the frequency list; it has depths $h$ when every index occurs at exactly one leaf and leaf $i$ has depth $h_i$. The weight of a node is the sum of the frequencies of the leaves below it, and the level weights at depth $h^*$ list the weights of the nodes at that depth.
--
--   For an optimal depth vector $h$, a depth $h^*$ and $0\le r\le 2^{h^*}$,
--   $$P(r)=\min\Big\{\sum_{i\in S}f_i:\ S\ \text{a set of leaves},\ \sum_{i\in S}2^{-h_i}=r\,2^{-h^*}\Big\},\qquad P(0)=0,$$
--   with value $\infty$ when no set reaches the target exactly. $h_{\min}$ and $h_{\max}$ are the minimum and maximum depths.
--
--   A density order lists every leaf once, in nondecreasing order of $f_i/2^{-h_i}$, with any fixed tie order. The fractional greedy for the target $r2^{-h^*}$ selects leaves along it; the leaves it selects completely are the longest prefix of the order whose Kraft sum $\sum 2^{-h_i}$ is at most the target. The partially selected leaf, if any, is excluded.
--
--   **Formalization Note** Kraft values are rationals; $P(r)$ takes values in $\mathbb N\cup\{\infty\}$.
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, §6, Eq. (7), pp. 26–28 (PDF 27–29)

import Definitions.Def_HuffmanMPC_Main_Budgets

set_option autoImplicit false

namespace HuffmanMPC.Main

/-- A concrete finite full binary tree, labelled by occurrence indices. -/
inductive CodingTree (m : ℕ) where
  | leaf (i : Fin m)
  | node (left right : CodingTree m)

def CodingTree.leafPaths {m : ℕ} : CodingTree m → List (Fin m × List Bool)
  | .leaf i => [(i, [])]
  | .node l r =>
    (l.leafPaths.map fun x => (x.1, false :: x.2)) ++
      (r.leafPaths.map fun x => (x.1, true :: x.2))

def CodingTree.HasDepths {a : Frequencies} (t : CodingTree a.length)
    (h : Fin a.length → ℕ) : Prop :=
  (t.leafPaths.map Prod.fst).Perm (List.finRange a.length) ∧
    ∀ z ∈ t.leafPaths, z.2.length = h z.1

def CodingTree.weight {a : Frequencies} (t : CodingTree a.length) : ℕ :=
  (t.leafPaths.map fun z => a[z.1]).sum

def CodingTree.levelWeights {a : Frequencies} : CodingTree a.length → ℕ → List ℕ
  | t, 0 => [t.weight]
  | .leaf _, _+1 => []
  | .node l r, h+1 => l.levelWeights h ++ r.levelWeights h

noncomputable def kraft (h : ℕ) : ℚ := (2 : ℚ) ^ (-(h : ℤ))

def selectedCost (a : Frequencies) (s : Finset (Fin a.length)) : ℕ := ∑ i ∈ s, a[i]
noncomputable def selectedKraft {m : ℕ} (h : Fin m → ℕ) (s : Finset (Fin m)) : ℚ :=
  ∑ i ∈ s, kraft (h i)

/-- A finite exact-width optimum. Infeasible targets remain infinity. -/
noncomputable def prefixOptimum (a : Frequencies) (h : Fin a.length → ℕ)
    (star r : ℕ) : ℕ∞ :=
  ⨅ s : {s : Finset (Fin a.length) // selectedKraft h s = r * kraft star},
    (selectedCost a s.val : ℕ∞)

noncomputable def maxDepth {m : ℕ} (h : Fin m → ℕ) : ℕ := Finset.univ.sup h
noncomputable def minDepth {m : ℕ} (h : Fin m → ℕ) : ℕ :=
  sInf (Set.range h)

/-- A density order for the fractional greedy: every leaf exactly once, in
nondecreasing order of frequency per unit of Kraft value `f i / 2^(-h i)`.
Ties may be broken in any fixed way. -/
def IsDensityOrder (a : Frequencies) (h : Fin a.length → ℕ) (order : List (Fin a.length)) : Prop :=
  order.Perm (List.finRange a.length) ∧
    order.Pairwise fun i j => ((a[i] : ℕ) : ℚ) / kraft (h i) ≤ ((a[j] : ℕ) : ℚ) / kraft (h j)

/-- The leaves selected completely by the fractional greedy along `order` for the
target `r * 2^(-star)`: the longest prefix of `order` whose Kraft sum is at most
the target.  A partially selected leaf fails this test and is excluded. -/
noncomputable def greedyComplete {m : ℕ} (h : Fin m → ℕ) (order : List (Fin m))
    (star r : ℕ) : Finset (Fin m) :=
  ((List.range order.length).filterMap fun k =>
    if ((order.take (k+1)).map fun i => kraft (h i)).sum ≤ r * kraft star
    then order[k]? else none).toFinset

end HuffmanMPC.Main


