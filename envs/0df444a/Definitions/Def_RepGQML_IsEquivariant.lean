-- Prove2me | Definitions.Def_RepGQML_IsEquivariant
-- name    : RepGQML_IsEquivariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:25.595624+00:00
-- url     : https://prove2.me/theorems/10317087-bafa-449e-8437-79d7c22b2c86
-- title:
--   Equivariant map between group representations
-- statement:
--   Let $R$ and $S$ be representations of a group $G$ on vector spaces $V_R$ and $V_S$. A linear map $\varphi:V_R\to V_S$ is **equivariant** when
--   $$
--   \varphi\circ R_g=S_g\circ\varphi\qquad\text{for all } g\in G.
--   $$
--   Schur's lemma and the structure of the commutant are statements about these maps.
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Definition 16, p.24

import Mathlib

namespace RepGQML

/-- A linear map `φ : V → W` is **equivariant** between representations `ρ` and `σ` of `G` when
`φ ∘ ρ_g = σ_g ∘ φ` for all `g ∈ G` (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, Definition 16, p.24). -/
def IsEquivariant {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (ρ : Representation k G V) (σ : Representation k G W)
    (φ : V →ₗ[k] W) : Prop :=
  ∀ g : G, φ ∘ₗ ρ g = σ g ∘ₗ φ

end RepGQML


