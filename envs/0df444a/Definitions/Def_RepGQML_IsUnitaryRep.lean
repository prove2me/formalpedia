-- Prove2me | Definitions.Def_RepGQML_IsUnitaryRep
-- name    : RepGQML_IsUnitaryRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:25.465511+00:00
-- url     : https://prove2.me/theorems/3d3f9450-4590-4287-a30e-2e08102f9cb7
-- title:
--   Unitary representation
-- statement:
--   Let $V$ be a real or complex inner product space and $R$ a representation of a group $G$ on $V$. The representation is **unitary** when
--   $$
--   \langle R_g x, R_g y\rangle=\langle x,y\rangle\qquad\text{for all } g\in G,\ x,y\in V .
--   $$
--   Since $R_g$ is invertible, this says exactly that $R_g^\dagger R_g=\mathbb 1$ for all $g$, which is Definition 15 of the source. Unitary representations are the setting of every result of this mission.
--
--   **Formalization Note** The field is `RCLike`, because Definition 6 allows real or complex spaces. The source speaks of a Lie group; the predicate is stated for any group.
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Definition 15, p.23

import Mathlib

namespace RepGQML

/-- A representation `ρ` on an inner product space is **unitary** when every `ρ g` preserves the
inner product (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, Definition 15, p.23: `R†_g R_g = 1` for all `g`).

**Formalization Note** Since `ρ` is a homomorphism from a group, each `ρ g` is invertible, so
preserving the inner product is exactly `R†_g R_g = 1`. Def 6 (p.9) allows real or complex `V`, hence
`RCLike`. Def 15 speaks of a Lie group; the predicate is stated for any group. -/
def IsUnitaryRep {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (ρ : Representation 𝕜 G V) : Prop :=
  ∀ (g : G) (x y : V), inner 𝕜 (ρ g x) (ρ g y) = inner 𝕜 x y

end RepGQML


