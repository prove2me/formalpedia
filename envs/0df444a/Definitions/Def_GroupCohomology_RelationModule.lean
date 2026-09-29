-- Prove2me | Definitions.Def_GroupCohomology_RelationModule
-- name    : GroupCohomology_RelationModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/e1c43c00-9628-5e44-b386-a0ae5f4010c6
-- title:
--   Relation module and canonical free presentation of a representation
-- statement:
--   Fix a commutative ring $k$ and a group $G$, and let $B$ be a $k$-linear representation of $G$. Mathlib's $\mathrm{Rep}.\mathrm{free}\ k\ G\ B$ is the free $k[G]$-module on the underlying type of $B$; [`Rep.freeCover`](../def/GroupCohomology_RelationModule.html#L15) is the morphism $\varepsilon_B \colon k[G]^{(B)} \to B$ obtained by freely extending the identity map of the underlying set of $B$, so that the basis element indexed by $b$ goes to $b$. [`Rep.relationModule`](../def/GroupCohomology_RelationModule.html#L18) is the subrepresentation of $k[G]^{(B)}$ carried by $\ker \varepsilon_B$, the stability of this kernel under the $G$-action being exactly the equivariance of $\varepsilon_B$; [`Rep.relationModule.ι`](../def/GroupCohomology_RelationModule.html#L23) is the inclusion of this subrepresentation, and two small lemmas record that its underlying map is the coercion of a kernel element and that $\varepsilon_B$ annihilates the image. [`Rep.relationSeq`](../def/GroupCohomology_RelationModule.html#L32) assembles these into a short complex $R(B) \to k[G]^{(B)} \to B$ in $\mathrm{Rep}\ k\ G$ with $\varepsilon_B \circ \iota = 0$; five further lemmas identify its three terms and two maps with the objects just named.
--
--   A second section repackages the case $k = \mathbb{Z}$. [`Rep.relationCarrier`](../def/GroupCohomology_RelationModule.html#L50) is a type synonym for the relation module equipped only with its additive group structure, so that the $\mathbb{Z}$-module structure used on it is the canonical one on an abelian group; [`Rep.relationRepInt`](../def/GroupCohomology_RelationModule.html#L55) is the action of $G$ on this carrier, each $\rho(g)$ being the additive map underlying the action on `relationModule` regarded as $\mathbb{Z}$-linear, with the multiplicativity and unit laws inherited. [`Rep.relationModuleInt`](../def/GroupCohomology_RelationModule.html#L73) is the resulting object of $\mathrm{Rep}\ \mathbb{Z}\ G$, [`Rep.relationModuleInt.ι`](../def/GroupCohomology_RelationModule.html#L75) the corresponding inclusion into $\mathbb{Z}[G]^{(B)}$, and, after the lemma that the composite with $\varepsilon_B$ vanishes, [`Rep.relationSeqInt`](../def/GroupCohomology_RelationModule.html#L84) the associated short complex.
--
--   **Relation to Mathlib.** Built on Mathlib's `Rep.free` and `Rep.freeLift` and on `Representation.subrepresentation`; the free cover $\varepsilon_B$, the relation module and the presentation short complex are the project's own definitions.
--
--   **Where it is used.** The presentation $R(B) \to \mathbb{Z}[G]^{(B)} \to B$ is the device by which cohomological statements available for $\mathbb{Z}$-free coefficients are transferred to finite coefficient modules: with the middle term $\mathbb{Z}[G]$-free, dimension shifting along the sequence moves duality and Tate–Nakayama type results from $R(B)$ to $B$, in the Galois-cohomological input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_RelationModule.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

def freeCover (B : Rep.{u} k G) : Rep.free k G B ⟶ B :=
  Rep.freeLift k G B (fun b : B => b)

abbrev relationModule (B : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (Representation.subrepresentation (Rep.free k G B).ρ (LinearMap.ker (freeCover B).hom.toLinearMap) fun g x hx => by
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply] at hx ⊢
    rw [Rep.hom_comm_apply, hx, map_zero])

def relationModule.ι (B : Rep.{u} k G) : relationModule B ⟶ Rep.free k G B :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

theorem relationModule.ι_hom_apply (B : Rep.{u} k G) (x : relationModule B) :
    (relationModule.ι B).hom x = (x : Rep.free k G B) := rfl

theorem freeCover_hom_apply_ι (B : Rep.{u} k G) (x : relationModule B) :
    (freeCover B).hom ((relationModule.ι B).hom x) = 0 := x.2

abbrev relationSeq (B : Rep.{u} k G) : ShortComplex (Rep.{u} k G) where
  X₁ := relationModule B
  X₂ := Rep.free k G B
  X₃ := B
  f := relationModule.ι B
  g := freeCover B
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => x.2))

theorem relationSeq_X₁ (B : Rep.{u} k G) : (relationSeq B).X₁ = relationModule B := rfl
theorem relationSeq_X₂ (B : Rep.{u} k G) : (relationSeq B).X₂ = Rep.free k G B := rfl
theorem relationSeq_X₃ (B : Rep.{u} k G) : (relationSeq B).X₃ = B := rfl
theorem relationSeq_f (B : Rep.{u} k G) : (relationSeq B).f = relationModule.ι B := rfl
theorem relationSeq_g (B : Rep.{u} k G) : (relationSeq B).g = freeCover B := rfl

section Int

variable {G : Type} [Group G]

def relationCarrier (B : Rep ℤ G) : Type := relationModule B

instance relationCarrier.instAddCommGroup (B : Rep ℤ G) : AddCommGroup (relationCarrier B) :=
  inferInstanceAs (AddCommGroup (relationModule B))

def relationRepInt (B : Rep ℤ G) : Representation ℤ G (relationCarrier B) where
  toFun g := (((relationModule B).ρ g).toAddMonoidHom).toIntLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    change ((relationModule B).ρ 1) x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change ((relationModule B).ρ (g * h)) x = ((relationModule B).ρ g) (((relationModule B).ρ h) x)
    rw [map_mul]
    rfl

theorem relationRepInt_apply (B : Rep ℤ G) (g : G) (x : relationCarrier B) :
    relationRepInt B g x = ((relationModule B).ρ g : relationModule B → relationModule B) x := rfl

abbrev relationModuleInt (B : Rep ℤ G) : Rep ℤ G := Rep.of (relationRepInt B)

def relationModuleInt.ι (B : Rep ℤ G) : relationModuleInt B ⟶ Rep.free ℤ G B :=
  Rep.ofHom ⟨((relationModule.ι B).hom.toLinearMap.toAddMonoidHom).toIntLinearMap, fun _ => rfl⟩

theorem relationModuleInt.ι_hom_apply (B : Rep ℤ G) (x : relationModuleInt B) :
    (relationModuleInt.ι B).hom x = (relationModule.ι B).hom (show relationModule B from x) := rfl

theorem relationModuleInt_ι_comp_freeCover (B : Rep ℤ G) : relationModuleInt.ι B ≫ freeCover B = 0 :=
  Rep.hom_ext (DFunLike.ext _ _ fun x => freeCover_hom_apply_ι B (show relationModule B from x))

abbrev relationSeqInt (B : Rep ℤ G) : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (relationModuleInt.ι B) (freeCover B) (relationModuleInt_ι_comp_freeCover B)

end Int

end Rep

end


