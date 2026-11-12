-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ElementaryAbelianRepresentation
-- name    : OddOrder_GroupTheory_RepresentationTheory_ElementaryAbelianRepresentation
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:48:53.446483+00:00
-- url     : https://prove2.me/theorems/2379621f-3d28-458d-a686-b780f9b041bd
-- title:
--   $\mathbb{Z}/n$-modules with a group action: the missing `SMulCommClass`
-- statement:
--   For BG Theorem 3.7 (Frobenius kernel nilpotency), the coprime chief-factor case views a chief factor, an elementary abelian $p$-group $M$ with a conjugation action of the ambient group $G$, as a $\mathbb{Z}/p$-linear $G$-representation on $\mathrm{Additive}\,M$, so that BG Lemma 3.3 applies. This file supplies the instances needed for that.
--
--   Instances include `Additive.instDistribMulActionOfMulDistribMulAction` (a multiplicative action on a `CommGroup` transports to a `DistribMulAction`) and `instSMulCommClassZModOfDistribMulAction`; the definition `mulDistribMulActionQuotientOfTrivial` descends an action to a quotient by a normal subgroup acting trivially.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ElementaryAbelianRepresentation.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ElementaryAbelianRepresentation.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_PRank
import Mathlib.RepresentationTheory.Basic

namespace OddOrder.GroupTheory

/-- A `MulDistribMulAction G M` on a `CommGroup` `M` transports to a `DistribMulAction` of `G` on
the additive group `Additive M`: `g` acts the same way, and distributing over `*` becomes
distributing over `+`. (mathlib only transports actions when `Additive`/`Multiplicative` is on the
acting side, so this acted-on-side transport is provided here.) -/
instance Additive.instDistribMulActionOfMulDistribMulAction {G M : Type*} [Monoid G] [CommGroup M]
    [MulDistribMulAction G M] : DistribMulAction G (Additive M) where
  smul g a := Additive.ofMul (g • a.toMul)
  one_smul a := by
    change Additive.ofMul ((1 : G) • Additive.toMul a) = a
    rw [one_smul]
    rfl
  mul_smul g h a := by
    change Additive.ofMul ((g * h) • Additive.toMul a)
      = Additive.ofMul (g • (h • Additive.toMul a))
    rw [mul_smul]
  smul_zero g := by
    change Additive.ofMul (g • (1 : M)) = Additive.ofMul (1 : M)
    rw [smul_one]
  smul_add g a b := by
    change Additive.ofMul (g • (Additive.toMul a * Additive.toMul b))
      = Additive.ofMul (g • Additive.toMul a * g • Additive.toMul b)
    rw [smul_mul']

/-- On any `ZMod n`-module `A` carrying a `DistribMulAction` of a monoid `G`, the group action and
the `ZMod n`-scalar action commute: each `g` acts by an additive endomorphism, which is
automatically `ZMod n`-linear (`ZMod.map_smul`). This is the `SMulCommClass` that
`Representation.ofDistribMulAction (ZMod n) G A` requires. -/
instance instSMulCommClassZModOfDistribMulAction {n : ℕ} {G A : Type*} [Monoid G]
    [AddCommGroup A] [Module (ZMod n) A] [DistribMulAction G A] :
    SMulCommClass G (ZMod n) A where
  smul_comm g c a := ZMod.map_smul (DistribSMul.toAddMonoidHom A g) c a

/-- Descend a `MulDistribMulAction G M` to the quotient `G ⧸ L` when the normal subgroup `L` acts
trivially on `M`. (Used in BG Theorem 3.7's coprime chief-factor case: the conjugation action of
`G` on a chief factor `V` factors through `Ḡ = G/L` because `L` centralizes `V`.) -/
@[reducible]
noncomputable def mulDistribMulActionQuotientOfTrivial {G M : Type*} [Group G] [Monoid M]
    [MulDistribMulAction G M] (L : Subgroup G) [L.Normal]
    (hL : ∀ l : G, l ∈ L → ∀ m : M, l • m = m) :
    MulDistribMulAction (G ⧸ L) M :=
  MulDistribMulAction.compHom M
    (QuotientGroup.lift L (MulDistribMulAction.toMulAut G M)
      (fun l hl => MulEquiv.ext (fun m => by simpa using hL l hl m)))

/-- The descended action of `G ⧸ L` on `M` agrees with the original `G`-action on representatives:
`⟦g⟧ • m = g • m`. -/
theorem mulDistribMulActionQuotientOfTrivial_smul_mk {G M : Type*} [Group G] [Monoid M]
    [MulDistribMulAction G M] {L : Subgroup G} [L.Normal]
    (hL : ∀ l : G, l ∈ L → ∀ m : M, l • m = m) (g : G) (m : M) :
    letI := mulDistribMulActionQuotientOfTrivial L hL
    (QuotientGroup.mk g : G ⧸ L) • m = g • m :=
  rfl

end OddOrder.GroupTheory


