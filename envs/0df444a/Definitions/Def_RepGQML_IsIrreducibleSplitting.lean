-- Prove2me | Definitions.Def_RepGQML_IsIrreducibleSplitting
-- name    : RepGQML_IsIrreducibleSplitting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:27.600525+00:00
-- url     : https://prove2.me/theorems/73a45f23-ee1e-4125-a862-fa1a7eca0c90
-- title:
--   Irreducible splitting of a representation
-- statement:
--   Let $R$ be a representation of $G$ on $V$. A family $W_1,\dots,W_n$ of invariant subspaces is an **irreducible splitting** when
--   $$
--   V=W_1\oplus\cdots\oplus W_n
--   $$
--   and each restriction $R|_{W_j}$ is irreducible. A representation with such a family is completely reducible.
--
--   **Formalization Note** The invariant subspaces are Mathlib's `Subrepresentation R`, the direct sum is `DirectSum.IsInternal`, and irreducibility is `Representation.IsIrreducible`, which requires a nonzero space. The case $n=0$ is the splitting of $V=0$.
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Definition 14, p.23, with Definitions 12–13, p.22

import Mathlib

namespace RepGQML

/-- A family `W₁, …, W_n` of invariant subspaces is an **irreducible splitting** of `V` when
`V = W₁ ⊕ ⋯ ⊕ W_n` and each restriction `ρ|_{W_j}` is irreducible (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, Definition 14, p.23, with
Definitions 12–13, p.22).

**Formalization Note** The invariant subspaces of Def 12 are Mathlib's `Subrepresentation ρ`. Mathlib's
`Representation.IsIrreducible` requires a nonzero space, whereas Def 13 read literally also admits
`V = 0`; a zero summand is therefore excluded here, and it would add nothing to the sum. `n = 0` is
allowed and is the splitting of `V = 0`. -/
def IsIrreducibleSplitting {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) {n : ℕ} (W : Fin n → Subrepresentation ρ) : Prop :=
  DirectSum.IsInternal (fun j => (W j).toSubmodule) ∧ ∀ j, (W j).toRepresentation.IsIrreducible

end RepGQML


