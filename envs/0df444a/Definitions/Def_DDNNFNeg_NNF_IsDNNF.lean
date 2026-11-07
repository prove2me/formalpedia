-- Prove2me | Definitions.Def_DDNNFNeg_NNF_IsDNNF
-- name    : DDNNFNeg_NNF_IsDNNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:21:26.630926+00:00
-- url     : https://prove2.me/theorems/668048e3-7c3a-4e85-ac34-d7ff8612b308
-- title:
--   Decomposable NNF (DNNF)
-- statement:
--   An NNF $C$ is **decomposable** (a **DNNF**) if every $\wedge$-gate is decomposable: for every $\wedge$-gate with children $i, j$,
--   $$
--   \mathrm{vars}(i) \cap \mathrm{vars}(j) = \emptyset .
--   $$
--
--   **Formalization Note** This predicate does not exclude constant leaves; the paper's DNNFs are the constant-free ones (`NNF.IsConstFree`). Statements that quantify over "every DNNF" may use `IsDNNF` alone, which is a larger class.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §3.1, p.8

import Mathlib
import Definitions.Def_DDNNFNeg_NNF_vars

namespace DDNNFNeg

/-- The NNF `C` is decomposable (a DNNF): at every `∧` gate the subcircuits rooted at its two
children mention disjoint sets of variables (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §3.1, p.8).

**Formalization Note** The condition is imposed on every gate of the array. The paper's NNF
has literal leaves only; that restriction is `NNF.IsConstFree`, stated separately, so
`IsDNNF` alone is the class of DNNFs that may also use constant leaves. -/
def NNF.IsDNNF {X : Type*} [DecidableEq X] (C : NNF X) : Prop :=
  ∀ k i j : Fin C.size, C.gate k = .and i j → Disjoint (C.vars i) (C.vars j)

end DDNNFNeg


