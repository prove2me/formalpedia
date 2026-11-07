-- Prove2me | Definitions.Def_PathORAMCap_Leaf
-- name    : PathORAMCap_Leaf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:11.341203+00:00
-- url     : https://prove2.me/theorems/2fb551a2-66fd-4997-8138-a0872e7179e3
-- title:
--   The Path ORAM tree: depth $L=\lceil\log_2 N\rceil$, leaves, nodes and longest common prefixes
-- statement:
--   Path ORAM stores at most $N\ge1$ blocks on a complete binary tree of depth
--
--   $$L=\lceil\log_2 N\rceil,$$
--
--   the smallest nonnegative integer with $2^L\ge N$; for $N=1$ the tree is the root alone. Nodes are named by their paths from the root, $0$ for a left step and $1$ for a right step: the root is the empty string $\varepsilon$, the children of $v$ are $v0$ and $v1$, and the leaves are the strings in $\{0,1\}^L$. We write $v\preceq w$ when $v$ is a prefix of $w$ (an ancestor, possibly equal), and $\mathrm{lcp}(y,x)$ for the longest common prefix of two leaves, the deepest node shared by their root-to-leaf paths.
--
--   These are the index sets of every object of the mission: the process, the target loads and the upward packing.
--
--   **Formalization Note** $L$ is `Nat.clog 2 N` (the ceiling logarithm). Leaves are `List.Vector Bool L`, nodes are `List Bool`, $v\preceq w$ is `List.IsPrefix`, and the node of depth $\ell$ on the path of a leaf $y$ is the prefix of length $\ell$.
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), §2.1, p.6 (PDF p.9); §4.3.1, p.16 (PDF p.19)

import Mathlib

set_option autoImplicit false

namespace PathORAMCap

/-- Depth of the Path ORAM tree for a database of at most `N` blocks: `L = ⌈log₂ N⌉`, the smallest
nonnegative integer with `2 ^ L ≥ N` (Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*,
STOC 2027 submission (manuscript sha256 1762f048…), §2.1, p.6 (PDF p.9)). For `N = 1` the tree is the
root alone (`L = 0`).

**Formalization Note.** `Nat.clog 2 N` is the ceiling logarithm (not the floor `Nat.log`). -/
def treeDepth (N : ℕ) : ℕ := Nat.clog 2 N

/-- A leaf of the depth-`L` tree: a bit string of length exactly `L` (`false` = a left step `0`,
`true` = a right step `1`), §2.1, p.6 (PDF p.9); §4.3.1, p.16 (PDF p.19).

**Formalization Note.** Nodes are bit strings `List Bool` (the root is `[]`, the children of `v`
are `v ++ [false]` and `v ++ [true]`), and `v <+: w` (`List.IsPrefix`) is the paper's `v ⪯ w`
("`v` is an ancestor of `w`, possibly equal to it"). The node of depth `ℓ` on the path of a leaf `y`
is `y.toList.take ℓ`. -/
abbrev Leaf (L : ℕ) : Type := List.Vector Bool L

/-- The longest common prefix of two bit strings. For two leaves `y, x` it is the node
`lcp(y, x)` of §4.3.1, p.16 (PDF p.19): the deepest node shared by their root-to-leaf paths. -/
def commonPrefix : List Bool → List Bool → List Bool
  | a :: as, b :: bs => if a = b then a :: commonPrefix as bs else []
  | _, _ => []

end PathORAMCap


