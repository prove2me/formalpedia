-- Prove2me | Definitions.Def_GroupCohomology_RepPi
-- name    : GroupCohomology_RepPi
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/0dda7dbf-1ae5-53c3-b265-4ce6ccc9e6d3
-- title:
--   Arbitrary products of representations in `Rep k G`
-- statement:
--   Fix a commutative ring $k$, a group $G$ and a family $(F_i)_{i \in \iota}$ of objects of `Rep k G`, i.e. $k$-modules with a $k$-linear $G$-action (all types in the same universe). `piRepresentation F` is the representation of $G$ on the product module $\prod_{i \in \iota} F_i$, realised as the dependent function type `(i : ι) → F i`, whose action of $g$ sends $x$ to the function $i \mapsto \rho_{F_i}(g)(x_i)$; `piRepresentation_apply` records this componentwise formula. `obj F` is the resulting object of `Rep k G`, and `obj_rho_apply` restates the formula for its action.
--
--   The remaining declarations equip `obj F` with the structure of a categorical product over the arbitrary index type $\iota$. For each $i$, `proj F i : obj F ⟶ F i` is the $G$-equivariant map given by evaluation at $i$. For an object $X$ of `Rep k G` and a family of morphisms $\varphi_i : X \to F_i$, `lift F φ : X ⟶ obj F` is the equivariant map $x \mapsto (i \mapsto \varphi_i(x))$, equivariance coming from that of each $\varphi_i$; `lift_proj` asserts that `lift F φ` followed by `proj F i` is $\varphi_i$, and `hom_ext` asserts that two morphisms $f, g : X \to \mathrm{obj}\,F$ agreeing after composition with every projection are equal. Thus `obj F`, together with the projections, satisfies the universal property of the product of the family $(F_i)$, stated in elementary form rather than as a `Limits` cone. Finally, for a second family $(F'_i)$ and morphisms $\varphi_i : F_i \to F'_i$, `map F φ : obj F ⟶ obj F'` is the morphism obtained by applying $\varphi_i$ in each coordinate, and `lift_hom_apply`, `proj_hom_apply`, `map_hom_apply` give the values of the underlying $k$-linear maps on components.
--
--   **Relation to Mathlib.** Mathlib's category `Rep k G` is used throughout; this module supplies an explicit model of the product of a family of representations indexed by an arbitrary type, with the product module as literal carrier, together with the projections and the lift/uniqueness property stated directly for morphisms rather than through Mathlib's limit API.
--
--   **Where it is used.** The explicit componentwise carrier is what allows $S$-idèle modules of class field theory, which are infinite products of coinduced local modules, to be manipulated coordinatewise, and it underlies the comparison of the cohomology (and, for finite $G$, the Tate cohomology in degrees $0$ and $-1$) of such a product with the cohomologies of its factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_RepPi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

namespace GroupCohomology.RepPi

variable {k G : Type u} [CommRing k] [Group G] {ι : Type u} (F : ι → Rep.{u} k G)

noncomputable def piRepresentation : Representation k G ((i : ι) → F i) where
  toFun g := LinearMap.pi fun i => ((F i).ρ g).comp (LinearMap.proj i)
  map_one' := LinearMap.ext fun x => funext fun i => by simp
  map_mul' g h := LinearMap.ext fun x => funext fun i => by simp

@[simp] theorem piRepresentation_apply (g : G) (x : (i : ι) → F i) (i : ι) :
    piRepresentation F g x i = (F i).ρ g (x i) := rfl

noncomputable abbrev obj : Rep.{u} k G := Rep.of (piRepresentation F)

theorem obj_rho_apply (g : G) (x : obj F) (i : ι) : (obj F).ρ g x i = (F i).ρ g (x i) := rfl

noncomputable def proj (i : ι) : obj F ⟶ F i := Rep.ofHom ⟨LinearMap.proj i, fun _ => rfl⟩

@[simp] theorem proj_hom_apply (i : ι) (x : obj F) : (proj F i).hom x = x i := rfl

noncomputable def lift {X : Rep.{u} k G} (φ : (i : ι) → (X ⟶ F i)) : X ⟶ obj F :=
  Rep.ofHom ⟨LinearMap.pi fun i => (φ i).hom.toLinearMap, fun g => LinearMap.ext fun x => funext fun i =>
    Rep.hom_comm_apply (φ i) g x⟩

@[simp] theorem lift_hom_apply {X : Rep.{u} k G} (φ : (i : ι) → (X ⟶ F i)) (x : X) (i : ι) : (lift F φ).hom x i = (φ i).hom x := rfl

theorem lift_proj {X : Rep.{u} k G} (φ : (i : ι) → (X ⟶ F i)) (i : ι) : lift F φ ≫ proj F i = φ i :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

theorem hom_ext {X : Rep.{u} k G} {f g : X ⟶ obj F} (h : ∀ i, f ≫ proj F i = g ≫ proj F i) : f = g :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => funext fun i => by
    have := congrArg (fun ψ : X ⟶ F i => ψ.hom x) (h i)
    exact this))

noncomputable def map {F' : ι → Rep.{u} k G} (φ : (i : ι) → (F i ⟶ F' i)) : obj F ⟶ obj F' :=
  lift F' fun i => proj F i ≫ φ i

@[simp] theorem map_hom_apply {F' : ι → Rep.{u} k G} (φ : (i : ι) → (F i ⟶ F' i)) (x : obj F) (i : ι) :
    (map F φ).hom x i = (φ i).hom (x i) := rfl

end GroupCohomology.RepPi


