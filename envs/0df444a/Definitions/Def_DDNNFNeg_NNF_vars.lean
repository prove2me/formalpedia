-- Prove2me | Definitions.Def_DDNNFNeg_NNF_vars
-- name    : DDNNFNeg_NNF_vars
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:19.67689+00:00
-- url     : https://prove2.me/theorems/7fe27483-fa05-46d1-a4d4-5ce2b958d191
-- title:
--   Variables mentioned by a subcircuit
-- statement:
--   For a gate $k$ of an NNF $C$, $\mathrm{vars}(k) \subseteq X$ is the set of variables **mentioned** by the subcircuit rooted at $k$: $\{v\}$ for a literal on $v$, $\emptyset$ for a constant, and $\mathrm{vars}(i) \cup \mathrm{vars}(j)$ for an $\wedge$- or $\vee$-gate with children $i, j$.
--
--   This is the syntactic notion used to define decomposability ("the subcircuits rooted at its children mention disjoint sets of variables"), not semantic dependence.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §3.1, p.8

import Mathlib
import Definitions.Def_DDNNFNeg_NNF

namespace DDNNFNeg

/-- The set of variables mentioned by the subcircuit of `C` rooted at gate `k`
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §3.1, p.8: "the subcircuits rooted at its children mention disjoint sets of
variables"): a literal on `v` mentions `{v}`, a constant mentions no variable, and an
`∧`/`∨` gate mentions the union of what its two children mention.

**Formalization Note** This is the syntactic notion (variables occurring in the subcircuit),
not semantic dependence. -/
def NNF.vars {X : Type*} [DecidableEq X] (C : NNF X) (k : Fin C.size) : Finset X :=
  match h : C.gate k with
  | .lit v _ => {v}
  | .const _ => ∅
  | .and i j =>
      have hij := C.wf k i j (Or.inl h)
      C.vars i ∪ C.vars j
  | .or i j =>
      have hij := C.wf k i j (Or.inr h)
      C.vars i ∪ C.vars j
termination_by k.val
decreasing_by
  · exact hij.1
  · exact hij.2
  · exact hij.1
  · exact hij.2

end DDNNFNeg


