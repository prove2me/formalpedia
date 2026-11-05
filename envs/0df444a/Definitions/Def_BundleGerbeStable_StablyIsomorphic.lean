-- Prove2me | Definitions.Def_BundleGerbeStable_StablyIsomorphic
-- name    : BundleGerbeStable_StablyIsomorphic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:03.070755+00:00
-- url     : https://prove2.me/theorems/128eef7c-e9b6-4be2-b0dd-f906bfa8b4be
-- title:
--   Stable isomorphism of bundle gerbes (Definition 3.1)
-- statement:
--   Two bundle gerbes $(P,Y)$ and $(Q,Z)$ are **stably isomorphic** if there are trivial bundle gerbes $T_1,T_2$ such that
--   $$P\otimes T_1 \cong Q\otimes T_2.$$
--   In this mission, $Y$, $Z$ and the spaces of $T_1,T_2$ belong to an admissible class $\mathcal A$; `GerbeOver 𝒜` is the type of bundle gerbes over members of $\mathcal A$.
--
--   This is the equivalence relation whose classes Theorem 3.3 identifies with $H^3(M,\mathbb Z)$.
--
--   **Formalization Note.** The paper prints "$=$"; it is read as "isomorphic". The proof of Proposition 3.2 writes $P\otimes(Q^*\otimes Q)=Q\otimes(P\otimes Q^*)$, whose two sides live over different spaces, so literal equality cannot be meant.
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, Definition 3.1, p.4

import Mathlib
import Definitions.Def_BundleGerbeStable_Iso
import Definitions.Def_BundleGerbeStable_IsTensor
import Definitions.Def_BundleGerbeStable_IsDelta
import Definitions.Def_BundleGerbeStable_Admissible

namespace BundleGerbeStable

universe u

variable {M : Type u} [TopologicalSpace M] [DiffeologicalSpace M]

/-- A bundle gerbe over a member of the admissible class `𝒜`. -/
abbrev GerbeOver (𝒜 : AdmissibleClass M) : Type (u + 1) :=
  Σ S : {S : LocallySplit M // 𝒜.mem S}, BundleGerbe S.1

/-- **Stable isomorphism** (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local theory*,
arXiv:math/9908135v1, Definition 3.1, p.4): `(P, Y)` and `(Q, Z)` "are called stably isomorphic if there
are trivial bundle gerbes T₁ and T₂ such that P ⊗ T₁ = Q ⊗ T₂".

**Formalization Note.** The "=" of the paper is read as "isomorphic": the proof of Proposition 3.2
writes `P ⊗ (Q* ⊗ Q) = Q ⊗ (P ⊗ Q*)`, whose sides live over different spaces. `T₁`, `T₂` range over
gerbes on members of `𝒜`, and need not lie over `Y` or `Z`. -/
def StablyIsomorphic (𝒜 : AdmissibleClass M) (P Q : GerbeOver 𝒜) : Prop :=
  ∃ (S₁ S₂ : LocallySplit M) (_ : 𝒜.mem S₁) (_ : 𝒜.mem S₂)
    (T₁ : BundleGerbe S₁) (T₂ : BundleGerbe S₂)
    (G₁ : BundleGerbe (fibreProd P.1.1 S₁)) (G₂ : BundleGerbe (fibreProd Q.1.1 S₂)),
    IsTrivial T₁ ∧ IsTrivial T₂ ∧ IsTensor G₁ P.2 T₁ ∧ IsTensor G₂ Q.2 T₂ ∧ Nonempty (Iso G₁ G₂)

end BundleGerbeStable


