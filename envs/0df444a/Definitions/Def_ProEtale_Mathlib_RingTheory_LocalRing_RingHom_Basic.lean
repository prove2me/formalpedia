-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_LocalRing_RingHom_Basic
-- name    : ProEtale_Mathlib_RingTheory_LocalRing_RingHom_Basic
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:00:26.531801+00:00
-- url     : https://prove2.me/theorems/8e1802f6-b162-59d3-a9f7-43ab82e278ac
-- title:
--   Membership in the maximal ideal can be tested along a local homomorphism of local rings
-- statement:
--   Let $g : R \to S$ be a local homomorphism between local commutative rings, meaning that $g$ maps non-units to non-units. For every $x \in R$,
--   $$g(x) \in \mathfrak m_S \iff x \in \mathfrak m_R,$$
--   where $\mathfrak m_R$ and $\mathfrak m_S$ are the maximal ideals.
--
--   This small helper is used when comparing local rings and their residue fields along local maps.
--
--   **Formalization Note** The theorem is `IsLocalRing.map_mem_maximalIdeal_iff`, assuming `[IsLocalRing R] [IsLocalRing S] [IsLocalHom g]`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/LocalRing/RingHom/Basic.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Membership in the maximal ideal along a local ring homomorphism

Small helper about `IsLocalHom`: for a local ring homomorphism between local rings,
membership in the maximal ideal can be tested after applying the map.
-/

namespace IsLocalRing

/-- For a local ring homomorphism `g : R →+* S` between local rings, an element `x`
lies in the maximal ideal of `R` if and only if `g x` lies in the maximal ideal of
`S`. -/
theorem map_mem_maximalIdeal_iff {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (g : R →+* S) [IsLocalHom g] (x : R) :
    g x ∈ maximalIdeal S ↔ x ∈ maximalIdeal R := by
  simp only [mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
  exact isUnit_map_iff g x

end IsLocalRing


