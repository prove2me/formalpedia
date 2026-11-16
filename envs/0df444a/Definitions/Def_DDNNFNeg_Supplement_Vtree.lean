-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_Vtree
-- name    : DDNNFNeg_Supplement_Vtree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:39:17.945188+00:00
-- url     : https://prove2.me/theorems/87426b94-029b-42b1-9bce-870a470b010f
-- title:
--   Vtree (binary tree with variable-labelled leaves)
-- statement:
--   A **vtree** over a set of variables $X$ is a full binary tree whose leaves are labelled by variables of $X$: it is either a single leaf labelled by some $x \in X$, or an internal node with a left subtree $T_\ell$ and a right subtree $T_r$, both vtrees.
--
--   Vtrees are the standard device (Pipatsrisawat–Darwiche; [AAC+24]) for describing how a structured decomposable circuit splits its variables at its $\wedge$-gates; the paper refers to them in §1 (p.4) and §6.2 (p.18).
--
--   **Formalization Note** The paper does not define vtrees itself. That the leaves are labelled by $X$ bijectively is the separate condition `Vtree.IsVtreeOver`.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §1 p.4 and §6.2 p.18 (standard notion of [AAC+24])

import Mathlib

namespace DDNNFNeg.Supplement

/-- A **vtree** over a set of variables `X` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §1 p.4 and §6.2 p.18, citing [AAC+24]):
a full binary tree whose leaves are labelled by variables. Here `leaf x` is a leaf labelled `x`
and `node l r` is an internal node with left subtree `l` and right subtree `r`.

**Formalization Note** The paper does not define vtrees; it uses the standard notion of the
cited literature (Pipatsrisawat–Darwiche). That the leaves are labelled bijectively by `X` is
`Vtree.IsVtreeOver`. -/
inductive Vtree (X : Type*) where
  /-- a leaf labelled by the variable `x` -/
  | leaf (x : X)
  /-- an internal node with left subtree `l` and right subtree `r` -/
  | node (l r : Vtree X)

end DDNNFNeg.Supplement


