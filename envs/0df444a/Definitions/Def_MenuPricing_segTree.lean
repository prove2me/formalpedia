-- Prove2me | Definitions.Def_MenuPricing_segTree
-- name    : MenuPricing_segTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:22:01.722339+00:00
-- url     : https://prove2.me/theorems/769bb7c3-8f57-4a65-874c-76c8c4bee759
-- title:
--   Subroutine 4 BuildSegTree — the segment tree $\mathcal T$ and the tree decomposition $\mathcal I_{\mathcal T}$
-- statement:
--   Given endpoints $p_0 < p_1 < \dots < p_N$, **Subroutine 4** builds the **segment tree** $\mathcal T$: the root is $[p_0, p_N)$, and a tree interval $[p_i, p_j)$ with $j - i \ge 2$ has the two children $[p_i, p_k)$ and $[p_k, p_j)$, $k = \lfloor (i+j)/2 \rfloor$; intervals with $j = i + 1$ are leaves. The root has depth $0$ and each child is one deeper than its parent. For $0 \le i < j \le N$ the **tree decomposition** $\mathcal I_{\mathcal T}[p_i, p_j)$ is $\{[p_i,p_j)\}$ if $[p_i,p_j)$ is a tree interval, and otherwise
--   $$
--   \mathcal I_{\mathcal T}[p_i, p_j) := \mathcal I_{\mathcal T}\big([p_i,p_j)\cap I_L\big) \cup \mathcal I_{\mathcal T}\big([p_i,p_j)\cap I_R\big),
--   $$
--   where $I$ is the smallest tree interval containing $[p_i, p_j)$ and $I_L, I_R$ are its children.
--
--   Algorithm 2 estimates the probability of every tree interval and combines the estimates along tree decompositions to estimate revenues (Eq. (5)).
--
--   **Formalization Note** The tree is combinatorial in the indices: a tree interval is a triple $(i, j, h)$ standing for $[p_i, p_j)$ at depth $h$, listed in preorder. The decomposition is computed by descending from the root: inside the tree interval containing $[p_i,p_j)$ it descends into a child that contains $[p_i,p_j)$, and splits at the midpoint index when neither child does. Since tree intervals are nested or disjoint, the node where it splits is the smallest tree interval containing $[p_i,p_j)$, so this is the decomposition of Subroutine 4.
-- source:
--   Dai, Lin, Slivkins, The Power of Two Choices in Dynamic Pricing (manuscript, sha256 2dbec470…), Subroutine 4, p.45 (PDF p.47)

import Mathlib

namespace MenuPricing

/-- Subroutine 4 BuildSegTree (manuscript sha256 2dbec470…, p.45), first part: the segment tree over
the endpoint indices, as the list of its tree intervals `(i, j, h)`, standing for `[p_i, p_j)` at
depth `h`, in preorder. `segTree i j h` is the subtree rooted at `[p_i, p_j)` of depth `h`: if
`j − i ≥ 2` its children are `[p_i, p_k)` and `[p_k, p_j)` with `k = ⌊(i+j)/2⌋`; otherwise it is a
leaf. The tree of `p_0 < ⋯ < p_N` is `segTree 0 N 0` (root depth `0`).

**Formalization Note** The tree is combinatorial in the indices; the price `p_i` of an index is
applied by the users. -/
def segTree (i j h : ℕ) : List (ℕ × ℕ × ℕ) :=
  if 2 ≤ j - i then
    (i, j, h) :: (segTree i ((i + j) / 2) (h + 1) ++ segTree ((i + j) / 2) j (h + 1))
  else [(i, j, h)]
termination_by j - i
decreasing_by all_goals omega

/-- Subroutine 4 BuildSegTree (manuscript sha256 2dbec470…, p.45), second part: the tree
decomposition `ℐ_𝒯[p_i, p_j)` of `[p_i, p_j)`, computed inside the subtree rooted at the tree
interval `[p_a, p_b)` of depth `h` that contains it: if `[p_i, p_j)` is that tree interval it is
`{[p_i, p_j)}`; if it lies inside one child, descend into it; otherwise `[p_a, p_b)` is the smallest
tree interval containing `[p_i, p_j)`, and `ℐ_𝒯[p_i, p_j) = ℐ_𝒯([p_i, p_j) ∩ I_L) ∪ ℐ_𝒯([p_i, p_j) ∩ I_R)`
with `[p_i, p_j) ∩ I_L = [p_i, p_k)` and `[p_i, p_j) ∩ I_R = [p_k, p_j)`. The decomposition of
`p_0 < ⋯ < p_N` is `decomp 0 N 0 i j` for `0 ≤ i < j ≤ N`.

**Formalization Note** Subroutine 4 fills a table in increasing order of `j − i`, looking up the
smallest tree interval containing `[p_i, p_j)`; descending from the root finds the same interval
(tree intervals are nested or disjoint), so this is the same decomposition. -/
def decomp (a b h i j : ℕ) : List (ℕ × ℕ × ℕ) :=
  if (i = a ∧ j = b) ∨ b - a < 2 then [(a, b, h)]
  else if j ≤ (a + b) / 2 then decomp a ((a + b) / 2) (h + 1) i j
  else if (a + b) / 2 ≤ i then decomp ((a + b) / 2) b (h + 1) i j
  else decomp a ((a + b) / 2) (h + 1) i ((a + b) / 2) ++ decomp ((a + b) / 2) b (h + 1) ((a + b) / 2) j
termination_by b - a
decreasing_by all_goals omega

end MenuPricing


