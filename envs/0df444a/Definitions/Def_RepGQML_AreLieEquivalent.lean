-- Prove2me | Definitions.Def_RepGQML_AreLieEquivalent
-- name    : RepGQML_AreLieEquivalent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:29.74805+00:00
-- url     : https://prove2.me/theorems/31d4b322-89d5-447d-884e-6e883ed71e52
-- title:
--   Equivalent Lie algebra representations
-- statement:
--   Two representations $r$ and $s$ of a Lie algebra are **equivalent** when there is an invertible equivariant linear map between their spaces.
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Definition 16, p.24

import Mathlib
import Definitions.Def_RepGQML_IsLieEquivariant

namespace RepGQML

/-- Two Lie algebra representations are **equivalent** when an invertible equivariant map exists
between them (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, Definition 16, p.24). -/
def AreLieEquivalent {L V W : Type*} [LieRing L] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (r : L →+ Module.End ℂ V) (s : L →+ Module.End ℂ W) : Prop :=
  ∃ φ : V →ₗ[ℂ] W, IsLieEquivariant r s φ ∧ Function.Bijective φ

end RepGQML


