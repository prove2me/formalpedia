-- Prove2me | Definitions.Def_TauCeti_GroupTheory_Index_Basic
-- name    : TauCeti_GroupTheory_Index_Basic
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:36:28.634477+00:00
-- url     : https://prove2.me/theorems/6148ddca-288f-4db2-9d74-4231340b45e9
-- title:
--   Consequences of the index formula
-- statement:
--   For a subgroup $H\leq G$, adjoining the center gives the subgroup $H\vee Z(G)$. This bundle also supplies finite-index and countability properties of subgroup inverse images and coset spaces. These facts support quotient constructions in the arithmetic argument.
--
--   **Formalization Note.** These declarations adapt the Tau Ceti contributors' source (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`): https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/GroupTheory/Index/Basic.lean. The finite-index inverse-image instance is a local compatibility helper derived from Mathlib's subgroup-index API; it is not claimed as an original Tau Ceti declaration.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/GroupTheory/Index/Basic.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Consequences of the index formula

Adjoining the centre to a finite-index subgroup keeps the index finite, since it only enlarges
the subgroup.

Because the order of a subgroup divides the order of the group -- with the index as cofactor --
invertibility of the order of a finite group in a semiring passes to every subgroup.

Adjoining a two-element subgroup `N ⊄ Γ` normalised by `Γ` is also quantified: `Γ` then has
relative index exactly `2` in `Γ ⊔ N`, so `Γ.index = 2 * (Γ ⊔ N).index`. Taking `N` to be the
centre gives the `Γ.withCenter` readings.

## Main results

* `Subgroup.mem_withCenter_iff`: an element of `Γ·Z(G)` is one of `Γ` times a central one.
* `TauCeti.index_eq_of_natCard_eq_mul`: cancel a known nonzero subgroup order from the
  order-index formula.
* `Subgroup.withCenter_le_iff`: the universal property — containing `Γ·Z(G)` is containing both.
* `Subgroup.withCenter_eq_self_iff`: adjoining the centre changes nothing exactly when the
  centre already lies inside `Γ`.
* `Subgroup.relIndex_sup_eq_two`, `Subgroup.index_eq_two_mul_index_sup`: the relative index `2`
  and the index doubling, for an `N` normalised by `Γ` whose elements are `1` and `a ∉ Γ`.
* `Subgroup.instCountableQuotient`: a coset space of a countable group is countable.
* `Subgroup.finiteIndex_of_finiteIndex_subgroupOf`: finite index composes along `V ≤ U ≤ G`.
* `Subgroup.finiteIndex_inf_comap`: `H ⊓ f⁻¹(K)` has finite index when `H` does and
  `K` has finite index relative to `f(H)`.
* `Subgroup.finiteIndex_of_map_eq`: the image of a finite-index subgroup under a surjective
  homomorphism has finite index.
* `MonoidHom.finiteIndex_range_comp`: finite index of ranges is preserved by composition
  with a homomorphism of finite-index range.
* `MonoidHom.mk_mul_out_bijective`: right cosets of a composite range are represented by
  products of representatives for the two successive ranges.
* `Subgroup.relIndex_withCenter_eq_two`, `Subgroup.index_eq_two_mul_index_withCenter`: the same
  two facts on `Γ.withCenter`, when the centre is `{1, a}`.
-/


 section

namespace Subgroup

universe u



end Subgroup

namespace MonoidHom

universe u v w

variable {A : Type u} {B : Type v} {C : Type w} [Group A] [Group B] [Group C]







end MonoidHom

namespace Subgroup

/-- The inverse image of a finite-index subgroup has finite index. -/
instance finiteIndex_comap {G H : Type*} [Group G] [Group H] (f : G →* H)
    (K : Subgroup H) [K.FiniteIndex] : (K.comap f).FiniteIndex := by
  constructor
  rw [index_comap]
  have : K.IsFiniteRelIndex f.range := isFiniteRelIndex_of_finiteIndex
  exact IsFiniteRelIndex.relIndex_ne_zero

/-- **A coset space of a countable group is countable.** A countable group has only countably
many cosets of any subgroup. Where a construction runs over `G ⧸ H` one coset at a time it is
this that keeps the family countable — as in
`ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo`, which tiles a fundamental domain for
`H ≤ PSL(2, ℤ)` by one translate of `𝒟ᵒ` per coset. -/
@[to_additive /-- **A coset space of a countable additive group is countable.** A countable
additive group has only countably many cosets of any subgroup. -/]
instance instCountableQuotient {G : Type*} [Group G] [Countable G] (H : Subgroup G) :
    Countable (G ⧸ H) :=
  -- Stated as an instance because `G ⧸ H` reaches `Quotient` only through `HasQuotient`, which
  -- instance synthesis does not unfold: without this, `Countable (G ⧸ H)` is not found.
  inferInstanceAs (Countable (Quotient (QuotientGroup.leftRel H)))







/-- `Γ` with the centre of the ambient group adjoined. For `Γ ≤ SL(2, ℤ)` the centre is
`{±I}`, which acts trivially on `ℍ`; it is the cosets of `Γ·{±I}` — not those of `Γ` itself —
that name the distinct translates of `𝒟` tiling a `Γ` fundamental domain, since `q` and `-q`
would otherwise be counted as two cosets carrying the same translate. The two subgroups agree
exactly when `-I ∈ Γ`. -/
def withCenter {G : Type*} [Group G] (Γ : Subgroup G) : Subgroup G :=
  Γ ⊔ Subgroup.center G



/-- `Γ` sits inside `Γ` with the centre adjoined. -/
lemma le_withCenter {G : Type*} [Group G] (Γ : Subgroup G) : Γ ≤ Γ.withCenter :=
  le_sup_left









instance instFiniteIndexWithCenter {G : Type*} [Group G] (Γ : Subgroup G)
    [Γ.FiniteIndex] : Γ.withCenter.FiniteIndex :=
  Subgroup.finiteIndex_of_le Γ.le_withCenter

variable {G : Type*} [Group G] {Γ : Subgroup G} {a : G}









end Subgroup

namespace TauCeti





end TauCeti

end
end


