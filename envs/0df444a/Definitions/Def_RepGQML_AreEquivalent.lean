-- Prove2me | Definitions.Def_RepGQML_AreEquivalent
-- name    : RepGQML_AreEquivalent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:19.684848+00:00
-- url     : https://prove2.me/theorems/2b6ad2c2-88a3-48bc-bb8a-28d007a32cca
-- title:
--   Equivalent group representations
-- statement:
--   Two representations $R$ and $S$ of a group $G$ are **equivalent** (or isomorphic) when there is an invertible equivariant linear map $\varphi:V_R\to V_S$. Theorem 7 needs its irreps to be pairwise inequivalent in this sense.
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Definition 16, p.24

import Mathlib
import Definitions.Def_RepGQML_IsEquivariant

namespace RepGQML

/-- Two representations are **equivalent** (isomorphic) when an invertible equivariant map exists
between them (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, Definition 16, p.24). -/
def AreEquivalent {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (ρ : Representation k G V) (σ : Representation k G W) : Prop :=
  ∃ φ : V →ₗ[k] W, IsEquivariant ρ σ φ ∧ Function.Bijective φ

end RepGQML


