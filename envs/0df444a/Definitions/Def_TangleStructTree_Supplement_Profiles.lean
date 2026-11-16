-- Prove2me | Definitions.Def_TangleStructTree_Supplement_Profiles
-- name    : TangleStructTree_Supplement_Profiles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:10:10.750028+00:00
-- url     : https://prove2.me/theorems/75623236-8b21-47ab-8901-3f9f34f333b7
-- title:
--   Profiles, regular profiles and the set $\mathcal P_s$
-- statement:
--   Let $\vec S$ be a separation system in a universe $U$. Put
--
--   $$\mathcal P=\big\{\{\vec r,\vec s,\overleftarrow r\vee\overleftarrow s\}:\ \vec r,\vec s\in U\big\},\qquad \mathcal P_s=\big\{\{\vec r,\vec s,\overleftarrow t\}:\ \vec r,\vec s,\vec t\in U,\ \overleftarrow t\le\overleftarrow r\vee\overleftarrow s\big\}.$$
--
--   The **profiles** of $S$ are its $\mathcal P$-tangles. An oriented separation $\vec s$ is **small** if $\vec s\le\overleftarrow s$, and a profile is **regular** if none of its elements is small. A **$\mathcal P_s$-tree** of $\vec S$ is an $\mathcal F$-tree for $\mathcal F=\mathcal P_s$.
--
--   These are the objects of the profile duality theorem (Theorem 7.3).
--
--   **Formalization Note** Both families are given on $\vec S$: a subset of $\vec S$ belongs to the family iff its image in $U$ is such a triple. Elements that are not subsets of $\vec S$ never matter for orientations of $S$.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §7, pp.22–23 (PDF 33–34); small separations §2, p.3 (PDF 14)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_Supplement_SubSepSystem

namespace TangleStructTree

namespace Supplement

open SepSystem

variable {U : Type*} [Lattice U] [SepSystem U]

/-- "`P = {{r⃗, s⃗, r⃖ ∨ s⃖} : r⃗, s⃗ ∈ U}`, and refer to the `P`-tangles of `S` as its **profiles**"
(von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §7, p.22 (PDF 33)).

**Formalization Note** Only the elements of `P` that are subsets of `S⃗` matter for orientations of
`S`; `P` is therefore given on `S⃗` as the sets `σ ⊆ S⃗` whose image in `U` is such a triple. The
supremum is taken in `U`. -/
def profileFamily (S : SubSepSystem U) : Set (Set S.Carrier) :=
  {σ | ∃ r s : U, Subtype.val '' σ = {r, s, rev r ⊔ rev s}}

/-- "`P_s = {{r⃗, s⃗, t⃖} : r⃗, s⃗, t⃗ ∈ U and t⃖ ≤ r⃖ ∨ s⃖}`" (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §7, p.22 (PDF 33)),
given on `S⃗` as for `profileFamily`. -/
def strongFamily (S : SubSepSystem U) : Set (Set S.Carrier) :=
  {σ | ∃ r s t : U, Subtype.val '' σ = {r, s, rev t} ∧ rev t ≤ rev r ⊔ rev s}

/-- "A profile is **regular** if none of its elements is small", where `s⃗` is small if `s⃗ ≤ s⃖`
(von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §7, p.22 (PDF 33); §2, p.3 (PDF 14)). This predicate says that no element of
`τ` is small. -/
def NoSmall {S : SubSepSystem U} (τ : Set S.Carrier) : Prop :=
  ∀ x ∈ τ, ¬ x ≤ rev x

end Supplement

end TangleStructTree


