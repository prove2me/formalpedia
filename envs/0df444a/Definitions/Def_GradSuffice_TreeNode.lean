-- Prove2me | Definitions.Def_GradSuffice_TreeNode
-- name    : GradSuffice_TreeNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:22.446734+00:00
-- url     : https://prove2.me/theorems/6b2e621e-5818-4bb9-be32-b45fe12088a4
-- title:
--   Internal node of a complete binary tree
-- statement:
--   An internal node of the complete binary tree of depth $n$ is determined by its level $i\in\{0,\dots,n-1\}$ (0-based) and the sign prefix $\sigma_{<i}\in\{-1,1\}^i$ leading to it from the root; the root is the empty prefix.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §3.1, p.7

import Mathlib

namespace GradSuffice

/-- **Internal node of a complete binary tree of depth `n`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §3.1, p.7: "the functional
at the node reached after following that prefix"; a node is a level `i < n` together with the sign
prefix `σ<ᵢ` leading to it (the root is the empty prefix). -/
abbrev TreeNode (n : ℕ) : Type := Σ i : Fin n, (Fin i → Bool)

end GradSuffice


