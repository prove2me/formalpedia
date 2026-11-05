-- Prove2me | Definitions.Def_RepGQML_IsLieEquivariant
-- name    : RepGQML_IsLieEquivariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:33.566163+00:00
-- url     : https://prove2.me/theorems/bfade2a5-e63d-40a4-a58a-af7ff70fbca4
-- title:
--   Equivariant map between Lie algebra representations
-- statement:
--   Let $r$ and $s$ be representations of a Lie algebra $\mathfrak g$ on $V_r$ and $V_s$. A linear map $\varphi:V_r\to V_s$ is **equivariant** when $\varphi\circ r_X=s_X\circ\varphi$ for all $X\in\mathfrak g$.
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Definition 16, p.24

import Mathlib

namespace RepGQML

/-- A linear map `φ : V → W` is **equivariant** between Lie algebra representations `r` and `s` when
`φ ∘ r_X = s_X ∘ φ` for all `X` (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, Definition 16, p.24). -/
def IsLieEquivariant {L V W : Type*} [LieRing L] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (r : L →+ Module.End ℂ V) (s : L →+ Module.End ℂ W) (φ : V →ₗ[ℂ] W) : Prop :=
  ∀ X : L, φ ∘ₗ r X = s X ∘ₗ φ

end RepGQML


