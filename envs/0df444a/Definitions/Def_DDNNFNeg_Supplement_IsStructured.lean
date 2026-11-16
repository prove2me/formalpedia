-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_IsStructured
-- name    : DDNNFNeg_Supplement_IsStructured
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:43:09.41523+00:00
-- url     : https://prove2.me/theorems/d1d4fa9a-2c5b-4efc-b916-81b5bb3d23de
-- title:
--   Structured NNF
-- statement:
--   An NNF $C$ over the finite variable set $X$ is **structured** if there is one vtree $T$ over $X$ that $C$ respects. A **structured d-DNNF** in the sense of the paper is a d-DNNF (constant-free, decomposable, deterministic) that is structured.
--
--   Structured d-DNNFs are the circuit class of Theorems 1.2 and 6.6; they are closely related to unambiguous OBDDs and unambiguous finite automata.
--
--   **Formalization Note** The paper defers the definition to [AAC+24]; this is the standard one. Respecting a vtree implies decomposability, since the two sides of every split are disjoint.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §1 p.4 (standard notion of [AAC+24]); used in Theorems 1.2 (p.4) and 6.6 (p.18)

import Mathlib
import Definitions.Def_DDNNFNeg_Supplement_Vtree_IsVtreeOver
import Definitions.Def_DDNNFNeg_Supplement_RespectsVtree

namespace DDNNFNeg.Supplement

/-- The NNF `C` over the finite variable set `X` is **structured** (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §1 p.4, citing
[AAC+24]): it respects one vtree `T` over `X` (the same vtree for all its `∧`-gates).

A structured d-DNNF in the paper's sense is an NNF with `C.IsConstFree ∧ C.IsDDNNF ∧
IsStructured C`.

**Formalization Note** The paper only describes structuredness informally and defers to
[AAC+24]; this is the standard definition. Respecting a vtree implies decomposability, since
the two sides of every split are disjoint. -/
def IsStructured {X : Type*} [Fintype X] [DecidableEq X] (C : NNF X) : Prop :=
  ∃ T : Vtree X, T.IsVtreeOver ∧ RespectsVtree C T

end DDNNFNeg.Supplement


