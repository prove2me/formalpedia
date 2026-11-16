-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_Vtree_splits
-- name    : DDNNFNeg_Supplement_Vtree_splits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:40:47.470205+00:00
-- url     : https://prove2.me/theorems/b6c2152b-5bbe-4f97-97a6-b40f982aca44
-- title:
--   Splits of a vtree
-- statement:
--   For a vtree $T$, the list of **splits** contains, for every internal node $v$ of $T$ (the root included) with children $v_\ell, v_r$, the pair $(\mathrm{leaves}(v_\ell), \mathrm{leaves}(v_r))$ of variable sets below its left and right child. A leaf contributes no split.
--
--   The splits are the ways a structured circuit is allowed to divide its variables at an $\wedge$-gate.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §6.2 p.18 (standard notion of [AAC+24])

import Mathlib
import Definitions.Def_DDNNFNeg_Supplement_Vtree_leaves

namespace DDNNFNeg.Supplement

/-- The splits of the vtree `T` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §6.2, p.18; standard notion of [AAC+24]): one pair
`(leaves l, leaves r)` for every internal node `node l r` of `T` (the root included), listing
the variables below its left child and below its right child. -/
def Vtree.splits {X : Type*} [DecidableEq X] : Vtree X → List (Finset X × Finset X)
  | .leaf _ => []
  | .node l r => (l.leaves, r.leaves) :: (l.splits ++ r.splits)

end DDNNFNeg.Supplement


