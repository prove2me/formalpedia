-- Prove2me | Definitions.Def_GroupCohomology_RelationModuleRes
-- name    : GroupCohomology_RelationModuleRes
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/3967cb20-b934-5003-afd6-40f24df9ba5d
-- title:
--   Restriction maps on free covers and relation modules
-- statement:
--   Throughout, $k$ is a commutative ring, $G$ and $G'$ are groups and $\pi : G' \to G$ is a group homomorphism; $\mathrm{Res}_\pi$ denotes restriction of representations along $\pi$ (`Rep.res`, with functorial form `Rep.resFunctor`). For $B$ a $k$-linear representation of $G$, [`Rep.freeCover B`](../def/GroupCohomology_RelationModule.html#L15) is the augmentation $k[G]^{(B)} \to B$ sending the free generator at $b$ to $b$, and [`Rep.relationModule B`](../def/GroupCohomology_RelationModule.html#L18) is its kernel, regarded as a subrepresentation of the free representation on the underlying set of $B$.
--
--   [`Rep.freeResMap π B`](../def/GroupCohomology_RelationModuleRes.html#L16) is the morphism $k[G']^{(B)} \to \mathrm{Res}_\pi\, k[G]^{(B)}$ of representations of $G'$ determined by sending the free generator at $b$ (for $b$ in the underlying set of $B$) to the free generator at $b$ on the right-hand side. Two companion lemmas record that it is compatible with the augmentations: composing `freeResMap π B` with the restriction of `freeCover B` gives `freeCover (Rep.res π B)`, both as an equality of morphisms and in the pointwise form. Consequently `freeResMap π B` carries the kernel of the augmentation for $\mathrm{Res}_\pi B$ into the kernel of the augmentation for $B$, and [`Rep.relationModule.resMap π B`](../def/GroupCohomology_RelationModuleRes.html#L28) is the resulting morphism of representations of $G'$
--   $$\mathrm{relationModule}(\mathrm{Res}_\pi B) \longrightarrow \mathrm{Res}_\pi\, \mathrm{relationModule}(B),$$ whose underlying map is `freeResMap π B` applied to the underlying element of the free module.
--
--   [`Rep.resIhom π R X`](../def/GroupCohomology_RelationModuleRes.html#L39) is the comparison morphism $\mathrm{Res}_\pi \operatorname{Hom}_k(R,X) \to \operatorname{Hom}_k(\mathrm{Res}_\pi R, \mathrm{Res}_\pi X)$ between internal homs in the categories of representations; on underlying $k$-modules it is the identity, the content being that the conjugation action of $g \in G'$ through $\pi(g)$ agrees with the conjugation action for the restricted representations.
--
--   Finally, for groups $H', H$ in the lowest universe, a homomorphism $\varpi : H' \to H$ and $B : \mathrm{Rep}\,\mathbb{Z}\,H$, [`Rep.relationModuleInt.resMap`](../def/GroupCohomology_RelationModuleRes.html#L52) transports `relationModule.resMap` to the retyped integral relation module `relationModuleInt`, with the same underlying additive map.
--
--   **Relation to Mathlib.** The free representation `Rep.free`, its universal property `Rep.freeLift`, restriction `Rep.res`/`Rep.resFunctor` and the internal hom `ihom` are Mathlib's; the augmentation `freeCover`, the relation module and its integral retyping come from the project's own relation-module module, and the restriction comparison maps defined here are likewise the project's.
--
--   **Where it is used.** These maps are the transition (inflation-type) morphisms used to compare the relation-module presentations, and hence the associated Ext and cohomology groups, of a representation and of its restriction along a homomorphism of groups; they serve the Galois-cohomological limit arguments over towers of finite levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_RelationModuleRes.lean

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G G' : Type u} [CommRing k] [Group G] [Group G'] (π : G' →* G)

def freeResMap (B : Rep.{u} k G) : Rep.free k G' B ⟶ Rep.res π (Rep.free k G B) :=
  Rep.freeLift k G' (Rep.res π (Rep.free k G B)) (fun b : B => (Finsupp.single b (MonoidAlgebra.single (1 : G) (1 : k)) : Rep.free k G B))

theorem freeResMap_comp_resFunctor_map_freeCover (B : Rep.{u} k G) :
    freeResMap π B ≫ (Rep.resFunctor π).map (freeCover B) = freeCover (Rep.res π B) :=
  Rep.free_ext k G' _ _ _ (fun b => by simp [freeResMap, freeCover, Rep.resMap])

theorem freeCover_freeResMap_apply (B : Rep.{u} k G) (x : Rep.free k G' B) :
    (freeCover B).hom ((freeResMap π B).hom x) = (freeCover (Rep.res π B)).hom x := by
  have h := congrArg (fun φ => φ.hom x) (freeResMap_comp_resFunctor_map_freeCover π B)
  simpa [Rep.resMap] using h

def relationModule.resMap (B : Rep.{u} k G) : relationModule (Rep.res π B) ⟶ Rep.res π (relationModule B) :=
  Rep.ofHom ⟨LinearMap.codRestrict _ ((freeResMap π B).hom.toLinearMap ∘ₗ (Submodule.subtype _)) (fun x => by
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        Representation.IntertwiningMap.toLinearMap_apply]
      rw [freeCover_freeResMap_apply]
      exact x.2),
    fun g => LinearMap.ext fun x => Subtype.ext (Rep.hom_comm_apply (freeResMap π B) g (x : Rep.free k G' B))⟩

theorem relationModule.resMap_hom_apply_coe (B : Rep.{u} k G) (x : relationModule (Rep.res π B)) :
    ((relationModule.resMap π B).hom x : Rep.free k G B) = (freeResMap π B).hom (x : Rep.free k G' B) := rfl

def resIhom (R X : Rep.{u} k G) : Rep.res π ((ihom R).obj X) ⟶ (ihom (Rep.res π R)).obj (Rep.res π X) :=
  Rep.ofHom ⟨LinearMap.id, fun g => LinearMap.ext fun f => by
      change ((ihom R).obj X).ρ (π g) f = ((ihom (Rep.res π R)).obj (Rep.res π X)).ρ g f
      erw [Rep.ihom_obj_ρ_apply, Rep.ihom_obj_ρ_apply]
      simp [map_inv]⟩

theorem resIhom_hom_apply (R X : Rep.{u} k G) (f : Rep.res π ((ihom R).obj X)) :
    (resIhom π R X).hom f = (show (ihom (Rep.res π R)).obj (Rep.res π X) from f) := rfl

section Int

variable {H H' : Type} [Group H] [Group H'] (ϖ : H' →* H)

def relationModuleInt.resMap (B : Rep ℤ H) : relationModuleInt (Rep.res ϖ B) ⟶ Rep.res ϖ (relationModuleInt B) :=
  Rep.ofHom ⟨((relationModule.resMap ϖ B).hom.toLinearMap.toAddMonoidHom).toIntLinearMap,
    fun g => LinearMap.ext fun x =>
      (Rep.hom_comm_apply (relationModule.resMap ϖ B) g (show relationModule (Rep.res ϖ B) from x))⟩

theorem relationModuleInt.resMap_hom_apply (B : Rep ℤ H) (x : relationModuleInt (Rep.res ϖ B)) :
    (relationModuleInt.resMap ϖ B).hom x =
      (show Rep.res ϖ (relationModuleInt B) from
        (relationModule.resMap ϖ B).hom (show relationModule (Rep.res ϖ B) from x)) := rfl

end Int

end Rep

end


