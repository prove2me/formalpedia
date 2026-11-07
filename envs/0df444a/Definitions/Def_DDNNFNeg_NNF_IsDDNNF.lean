-- Prove2me | Definitions.Def_DDNNFNeg_NNF_IsDDNNF
-- name    : DDNNFNeg_NNF_IsDDNNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:22:45.483202+00:00
-- url     : https://prove2.me/theorems/26f02bf7-730f-4fd2-846d-09e270245780
-- title:
--   Deterministic DNNF (d-DNNF)
-- statement:
--   An NNF $C$ is a **deterministic DNNF** (**d-DNNF**) if it is a DNNF and every $\vee$-gate is deterministic: for every $\vee$-gate with children $i, j$ and every assignment $x \in \{0,1\}^X$, at most one of the two children evaluates to $1$ on $x$.
--
--   Determinism is a semantic condition over all assignments; decomposability is syntactic.
--
--   **Formalization Note** Constant leaves are excluded separately by `NNF.IsConstFree`.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §3.1, p.8

import Mathlib
import Definitions.Def_DDNNFNeg_NNF_eval
import Definitions.Def_DDNNFNeg_NNF_IsDNNF

namespace DDNNFNeg

/-- The NNF `C` is a deterministic DNNF (d-DNNF): it is decomposable, and every `∨` gate is
deterministic, i.e. on every assignment to the variables at most one of its two children
evaluates to `1` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §3.1, p.8).

**Formalization Note** Determinism is semantic and global (over all assignments `x : X → Bool`);
decomposability is syntactic (`NNF.vars`). Constant leaves are excluded separately by
`NNF.IsConstFree`. -/
def NNF.IsDDNNF {X : Type*} [DecidableEq X] (C : NNF X) : Prop :=
  C.IsDNNF ∧ ∀ k i j : Fin C.size, C.gate k = .or i j →
    ∀ x : X → Bool, ¬ (C.eval x i = true ∧ C.eval x j = true)

end DDNNFNeg


