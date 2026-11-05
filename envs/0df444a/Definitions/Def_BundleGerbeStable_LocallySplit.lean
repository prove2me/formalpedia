-- Prove2me | Definitions.Def_BundleGerbeStable_LocallySplit
-- name    : BundleGerbeStable_LocallySplit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:12.080926+00:00
-- url     : https://prove2.me/theorems/74a4ad94-0793-4ef6-9449-05c5b2be375c
-- title:
--   Locally split maps and fibre products over $M$
-- statement:
--   A map $\pi : Y\to M$ is **locally split** if for every $x\in M$ there are an open set $U\ni x$ and a smooth section $s : U\to Y$ of $\pi$. Here $Y$ is a diffeological space and $\pi$ is smooth. Such a map is necessarily surjective.
--
--   The **fibre product** of $\pi_Y : Y\to M$ and $\pi_Z : Z\to M$ is
--   $$Y\times_\pi Z=\{(y,z)\in Y\times Z : \pi_Y(y)=\pi_Z(z)\},$$
--   with the subspace diffeology; its projection to $M$ is again locally split. In particular $Y^{[2]}=Y\times_\pi Y$.
--
--   These are the spaces on which bundle gerbes live.
--
--   **Formalization Note.** $\pi$ is neither required to be a submersion nor a fibration. Page 2 says explicitly that it need not be a fibration. Its remark that a locally split map in the smooth category "is just a submersion" is a loose remark, not a statement this mission uses: $\mathbb R\sqcup\mathbb R\to\mathbb R$, the identity on one sheet and $x\mapsto x^2$ on the other, has local sections everywhere and is not a submersion. `AdmissibleClass` selects submersions if desired. $Y$ lives in the universe of $M$.
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.2 (locally split maps, fibre products)

import Mathlib
import Definitions.Def_BundleGerbeStable_Diffeologies

open Diffeology TopologicalSpace

namespace BundleGerbeStable

universe u

/-- A **locally split map** to `M` (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local
theory*, arXiv:math/9908135v1, §2, p.2): "for every x ∈ M there is an open set U containing x and a
local section s: U → Y".

**Formalization Note.** `Y` is a diffeological space, so that finite-dimensional and
infinite-dimensional manifolds and differentiable spaces (all named on p.2) are all covered. `π` is
neither required to be a submersion nor a fibration: p.2 says explicitly that it need not be a
fibration. `AdmissibleClass` selects the category of `Y`'s. -/
structure LocallySplit (M : Type u) [TopologicalSpace M] [DiffeologicalSpace M] where
  /-- The total space `Y`. -/
  Y : Type u
  /-- The diffeology of `Y`. -/
  [diff : DiffeologicalSpace Y]
  /-- The map `π : Y → M`. -/
  π : Y → M
  π_smooth : DSmooth π
  split : ∀ x : M, ∃ U : Opens M, x ∈ U ∧ ∃ s : U → Y, DSmooth s ∧ ∀ u : U, π (s u) = u

attribute [instance] LocallySplit.diff

variable {M : Type u} [TopologicalSpace M] [DiffeologicalSpace M]

/-- The fibre product `Y ×_π Z` (arXiv:math/9908135v1, §2, p.2) as a diffeological space. For `S = T`
it is `Y^[2]`. -/
abbrev FibreProd (S T : LocallySplit M) : Type u :=
  {q : S.Y × T.Y // S.π q.1 = T.π q.2}

/-- The fibre product of two locally split maps is locally split (arXiv:math/9908135v1, §2, pp.2–3). -/
def fibreProd (S T : LocallySplit M) : LocallySplit M where
  Y := FibreProd S T
  π := fun q ↦ S.π q.1.1
  π_smooth := S.π_smooth.comp (dSmooth_fst.comp dSmooth_subtype_val)
  split := fun x ↦ by
    obtain ⟨U, hxU, s, hs, hsπ⟩ := S.split x
    obtain ⟨V, hxV, r, hr, hrπ⟩ := T.split x
    refine ⟨U ⊓ V, ⟨hxU, hxV⟩, fun u ↦ ⟨(s ⟨u.1, u.2.1⟩, r ⟨u.1, u.2.2⟩), ?_⟩, ?_, ?_⟩
    · exact (hsπ ⟨u.1, u.2.1⟩).trans (hrπ ⟨u.1, u.2.2⟩).symm
    · refine DSmooth.subtype_mk' (DSmooth.prodMk' ?_ ?_) _
      · exact hs.comp (DSmooth.subtype_mk' dSmooth_subtype_val _)
      · exact hr.comp (DSmooth.subtype_mk' dSmooth_subtype_val _)
    · exact fun u ↦ hsπ _

end BundleGerbeStable


