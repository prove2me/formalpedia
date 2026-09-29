-- Prove2me | Definitions.Def_GroupCohomology_PoitouTate
-- name    : GroupCohomology_PoitouTate
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/977bf35e-350c-5697-891d-38df8e77b084
-- title:
--   Total localisation, total local pairing, Poitou–Tate orthogonality predicate
-- statement:
--   Fix a field $k$, a group $\Gamma$, an index type $\iota$ with groups $\Gamma_v$ and homomorphisms $\mathrm{loc}_v \colon \Gamma_v \to \Gamma$ (the intended picture being a global Galois group with its decomposition groups), and $k$-linear representations $M$, $M'$ of $\Gamma$. Three things are defined. First, `locTotal` is the $k$-linear map $H^1(\Gamma, M) \to \prod_v H^1(\Gamma_v, M|_{\Gamma_v})$ whose $v$-th component is the restriction map `locRes`, i.e. the map on $H^1$ induced functorially by $\mathrm{loc}_v$ together with the identity on the restricted representation; a companion lemma records this componentwise description. Second, given a family of $k$-bilinear pairings $\langle\cdot,\cdot\rangle_v \colon H^1(\Gamma_v, M|_{\Gamma_v}) \times H^1(\Gamma_v, M'|_{\Gamma_v}) \to k$ and $\iota$ finite, `totalPairing` is the bilinear pairing on the products obtained by summing the local pairings on matching components, so that its value on $(x,y)$ is $\sum_v \langle x_v, y_v\rangle_v$. Third, `IsPoitouTateOrthogonality` is a `Prop`-valued structure with two fields, each an equality of submodules expressed through the project's `orthogonal` operation (for a pairing $B$ and a submodule $L$, $\mathrm{orthogonal}\,B\,L$ is the submodule of vectors $w$ with $B x w = 0$ for all $x \in L$): the orthogonal complement of the image of `locTotal` for $M$ under the total pairing equals the image of `locTotal` for $M'$, and the orthogonal complement of the image of `locTotal` for $M'$ under the flipped total pairing equals the image of `locTotal` for $M$. Thus the structure carries, as hypotheses on the datum $(\mathrm{loc}, M, M', \langle\cdot,\cdot\rangle)$, the exact mutual-annihilator statement; it is a predicate, not a theorem proved here.
--
--   **Relation to Mathlib.** Mathlib supplies the group cohomology $H^1$ and its functoriality (`map`) and, through `Submodule.dualAnnihilator`, the orthogonality used by the project's `orthogonal`; it has no Poitou–Tate duality, so the total localisation map, the total local pairing and the orthogonality predicate are the project's own.
--
--   **Where it is used.** The total localisation map and total local pairing are the global-to-local data on which Selmer groups and their dual local conditions are built, and the orthogonality predicate is the duality input to the Greenberg–Wiles formula for the $k$-dimension of a Selmer group used in the $R = T$ argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_PoitouTate.lean

import Mathlib
import Definitions.Def_GroupCohomology_Selmer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ)

section TotalLocalization

variable (M : Rep k Γ)

noncomputable def locTotal : H1 M →ₗ[k] ∀ v, H1 (Rep.res (loc v) M) :=
  LinearMap.pi fun v => (locRes loc M v).hom

@[simp]
lemma locTotal_apply (x : H1 M) (v : ι) :
    locTotal loc M x v = (locRes loc M v).hom x := rfl

end TotalLocalization

section TotalPairing

variable [Fintype ι] (M M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

noncomputable def totalPairing :
    (∀ v, H1 (Rep.res (loc v) M)) →ₗ[k] (∀ v, H1 (Rep.res (loc v) M')) →ₗ[k] k :=
  ∑ v, (pairing v).compl₁₂ (LinearMap.proj v) (LinearMap.proj v)

@[simp]
lemma totalPairing_apply (x : ∀ v, H1 (Rep.res (loc v) M))
    (y : ∀ v, H1 (Rep.res (loc v) M')) :
    totalPairing loc M M' pairing x y = ∑ v, pairing v (x v) (y v) := by
  simp only [totalPairing, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.proj_apply]

structure IsPoitouTateOrthogonality : Prop where

  annihilator_fst :
    orthogonal (totalPairing loc M M' pairing) (LinearMap.range (locTotal loc M))
      = LinearMap.range (locTotal loc M')

  annihilator_snd :
    orthogonal (totalPairing loc M M' pairing).flip (LinearMap.range (locTotal loc M'))
      = LinearMap.range (locTotal loc M)

end TotalPairing

end groupCohomology


