-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_RespectsVtree
-- name    : DDNNFNeg_Supplement_RespectsVtree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:42:10.456517+00:00
-- url     : https://prove2.me/theorems/bd2f2956-c63d-43bb-9d28-38ab726eab4a
-- title:
--   NNF respecting a vtree
-- statement:
--   An NNF $C$ over $X$ **respects** a vtree $T$ if for every $\wedge$-gate of $C$ with children $i$ and $j$ there is an internal node $v$ of $T$, with children $v_\ell, v_r$, such that
--
--   $$\mathrm{vars}(i) \subseteq \mathrm{leaves}(v_\ell) \quad\text{and}\quad \mathrm{vars}(j) \subseteq \mathrm{leaves}(v_r),$$
--
--   where $\mathrm{vars}(i)$ is the set of variables mentioned by the subcircuit rooted at $i$. This is the standard (Pipatsrisawat–Darwiche) formalization of the paper's description "every AND gate over the same set of variables partitions its variables between its children in the same way" (p.4).
--
--   **Formalization Note** The condition is imposed on every $\wedge$-gate of the gate array. The children are ordered; swapping the two children of an $\wedge$-gate changes neither the function nor the size.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §1 p.4 (standard notion of [AAC+24])

import Mathlib
import Definitions.Def_DDNNFNeg_NNF_vars
import Definitions.Def_DDNNFNeg_Supplement_Vtree_splits

namespace DDNNFNeg.Supplement

/-- The NNF `C` respects the vtree `T` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §1 p.4: "every AND gate over the same set of
variables partitions its variables between its children in the same way [AAC+24]"; standard
Pipatsrisawat–Darwiche definition): for every `∧`-gate with children `i`, `j` there is an
internal node of `T` such that the variables mentioned below `i` label leaves under its left
child and those mentioned below `j` label leaves under its right child.

**Formalization Note** The condition is imposed on every `∧`-gate of the array, like
`NNF.IsDNNF`. The children are ordered (`i` left, `j` right); swapping the two children of an
`∧`-gate changes neither the function nor the size, so this is the standard notion. -/
def RespectsVtree {X : Type*} [DecidableEq X] (C : NNF X) (T : Vtree X) : Prop :=
  ∀ k i j : Fin C.size, C.gate k = .and i j →
    ∃ p ∈ T.splits, C.vars i ⊆ p.1 ∧ C.vars j ⊆ p.2

end DDNNFNeg.Supplement


