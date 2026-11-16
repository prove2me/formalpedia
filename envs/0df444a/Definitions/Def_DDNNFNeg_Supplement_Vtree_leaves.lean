-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_Vtree_leaves
-- name    : DDNNFNeg_Supplement_Vtree_leaves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:39:54.708429+00:00
-- url     : https://prove2.me/theorems/1640a4e2-5140-44c0-b411-81c89c2e42b9
-- title:
--   Variables at the leaves of a vtree
-- statement:
--   For a vtree $T$, $\mathrm{leaves}(T) \subseteq X$ is the set of variables labelling its leaves: $\mathrm{leaves}(x) = \{x\}$ for a leaf labelled $x$, and $\mathrm{leaves}(T_\ell, T_r) = \mathrm{leaves}(T_\ell) \cup \mathrm{leaves}(T_r)$ for an internal node.
--
--   This is the variable set "below" a vtree node, used to state when a circuit respects a vtree.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §6.2 p.18 (standard notion of [AAC+24])

import Mathlib
import Definitions.Def_DDNNFNeg_Supplement_Vtree

namespace DDNNFNeg.Supplement

/-- The set of variables labelling the leaves of the vtree `T` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §6.2, p.18; standard
notion of [AAC+24]). -/
def Vtree.leaves {X : Type*} [DecidableEq X] : Vtree X → Finset X
  | .leaf x => {x}
  | .node l r => l.leaves ∪ r.leaves

end DDNNFNeg.Supplement


