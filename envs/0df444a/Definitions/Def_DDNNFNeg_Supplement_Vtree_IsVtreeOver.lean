-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_Vtree_IsVtreeOver
-- name    : DDNNFNeg_Supplement_Vtree_IsVtreeOver
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:41:23.902706+00:00
-- url     : https://prove2.me/theorems/7d7eb12b-6131-4595-8150-a69c60ec9d85
-- title:
--   Vtree over a finite variable set
-- statement:
--   A vtree $T$ is a **vtree over** the finite set $X$ if its leaves are labelled bijectively by $X$: every variable of $X$ labels some leaf, and no variable labels two leaves.
--
--   **Formalization Note** Bijectivity is written as $\mathrm{leaves}(T) = X$ together with disjointness of $\mathrm{leaves}(v_\ell)$ and $\mathrm{leaves}(v_r)$ at every internal node $v$.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §6.2 p.18 (standard notion of [AAC+24])

import Mathlib
import Definitions.Def_DDNNFNeg_Supplement_Vtree_splits

namespace DDNNFNeg.Supplement

/-- `T` is a vtree over the finite variable set `X` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §6.2, p.18; standard notion of
[AAC+24]): its leaves are labelled bijectively by `X`.

**Formalization Note** Bijectivity is written as: every variable labels some leaf
(`T.leaves = univ`), and at every internal node the variables below the left child and those
below the right child are disjoint, so no variable labels two leaves. -/
def Vtree.IsVtreeOver {X : Type*} [Fintype X] [DecidableEq X] (T : Vtree X) : Prop :=
  T.leaves = Finset.univ ∧ ∀ p ∈ T.splits, Disjoint p.1 p.2

end DDNNFNeg.Supplement


