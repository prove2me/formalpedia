-- Prove2me | Definitions.Def_RepGQML_IsCompletelyReducible
-- name    : RepGQML_IsCompletelyReducible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:10.747102+00:00
-- url     : https://prove2.me/theorems/60f0ab56-bf15-4cbe-96e9-14e1b93f3bfd
-- title:
--   Completely reducible representation
-- statement:
--   A representation of $G$ on $V$ is **completely reducible** when $V$ is the direct sum of finitely many invariant subspaces on each of which the restriction is irreducible. In a suitable basis, all representatives are then simultaneously block diagonal with irreducible blocks.
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Definition 14, p.23

import Mathlib
import Definitions.Def_RepGQML_IsIrreducibleSplitting

namespace RepGQML

/-- A representation is **completely reducible** when `V` is a direct sum of finitely many invariant
subspaces on each of which the restriction is irreducible (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, Definition 14, p.23). -/
def IsCompletelyReducible {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : Prop :=
  ∃ (n : ℕ) (W : Fin n → Subrepresentation ρ), IsIrreducibleSplitting ρ W

end RepGQML


