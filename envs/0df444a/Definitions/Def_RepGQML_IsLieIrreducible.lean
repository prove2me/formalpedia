-- Prove2me | Definitions.Def_RepGQML_IsLieIrreducible
-- name    : RepGQML_IsLieIrreducible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:35.356677+00:00
-- url     : https://prove2.me/theorems/063c88b8-f8c3-4bba-b09f-24dba1e90eed
-- title:
--   Irreducible Lie algebra representation
-- statement:
--   A map $r$ from a Lie algebra to the operators on a complex vector space $V$ is **irreducible** when $V$ is nonzero and its only subspaces invariant under every $r(X)$ are $0$ and $V$.
--
--   **Formalization Note** The requirement that $V$ be nonzero matches Mathlib's `Representation.IsIrreducible`; Definition 13 read literally also admits $V=0$. Subspaces are complex subspaces.
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Definitions 12–13, p.22

import Mathlib

namespace RepGQML

/-- A map `r` from a Lie ring to the operators on `V` is **irreducible** when `V` is nonzero and its
only invariant complex subspaces are `0` and `V` (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, Definitions 12–13, p.22).

**Formalization Note** "Nonzero" matches Mathlib's `Representation.IsIrreducible`. Def 13 read
literally also admits `V = 0`. -/
def IsLieIrreducible {L V : Type*} [LieRing L] [AddCommGroup V] [Module ℂ V]
    (r : L →+ Module.End ℂ V) : Prop :=
  Nontrivial V ∧
    ∀ W : Submodule ℂ V, (∀ (X : L), ∀ v ∈ W, r X v ∈ W) → W = ⊥ ∨ W = ⊤

end RepGQML


