-- Prove2me | Definitions.Def_GroupCohomology_RepCokernel
-- name    : GroupCohomology_RepCokernel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/d17f9027-1c62-5947-9a24-c8cb18023425
-- title:
--   Explicit cokernel of a morphism of group representations
-- statement:
--   Fix a commutative ring $k$, a group $G$ and a morphism $f \colon X \to Y$ of $k$-linear representations of $G$ (objects of `Rep k G`). The module provides an explicit model of the cokernel of $f$, rather than appealing to the categorical cokernel. The object `obj f` is the representation whose underlying module is the quotient of the module $Y$ by the image submodule $\operatorname{range}(f)$, with the representation induced by $\rho_Y$; the fact that this image is $G$-stable is verified from the intertwining property of $f$, an element $f(a)$ being carried by $g$ to $f(\rho_X(g) a)$. The morphism `π f : Y ⟶ obj f` is the quotient map $Y \to Y/f(X)$, regarded as a morphism of representations; its underlying linear map sends $y$ to its class, is surjective (`π_hom_surjective`), and vanishes at $y$ exactly when $y$ lies in the image of $f$ (`π_hom_apply_eq_zero_iff`). The lemma `π_hom_apply` records that the underlying map of `π f` is the canonical quotient map on elements, so consumers may compute with representatives.
--
--   Finally, `seq f` packages $X \xrightarrow{f} Y \xrightarrow{\pi} Y/f(X)$ as a `ShortComplex` in `Rep k G`: a triple of objects together with the two morphisms and the proof that the composite is zero, the latter holding because every $f(x)$ has zero class. No exactness or short-exactness is asserted here; `seq f` is only a complex, whose middle and right-hand exactness (the latter from surjectivity of $\pi$) are available to users from the stated elementwise lemmas.
--
--   **Relation to Mathlib.** Mathlib's `Rep k G` has categorical cokernels; this module instead fixes an explicit carrier, the module quotient $Y/\operatorname{range}(f)$ with the induced action, via Mathlib's `Representation.quotient` and `Submodule.mkQ`, and assembles the resulting two-step complex as a Mathlib `ShortComplex`.
--
--   **Where it is used.** The explicit carrier makes the construction usable wherever quotient representations must be manipulated through representatives, for instance in forming the $S$-idèle class module $J_S/K_S$ and in quotients of lattices arising in Herbrand-quotient computations in Galois cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_RepCokernel.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory

namespace GroupCohomology.RepCokernel

universe u

variable {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)

noncomputable abbrev obj : Rep.{u} k G :=
  Rep.of (Representation.quotient Y.ρ (LinearMap.range f.hom.toLinearMap) fun g => by
    rintro _ ⟨a, rfl⟩
    exact ⟨X.ρ g a, Rep.hom_comm_apply f g a⟩)

noncomputable def π : Y ⟶ obj f := Rep.ofHom ⟨Submodule.mkQ _, fun _ => rfl⟩

theorem π_hom_apply (y : Y) : (π f).hom y = Submodule.Quotient.mk y := rfl

theorem π_hom_surjective : Function.Surjective (π f).hom := Submodule.mkQ_surjective _

theorem π_hom_apply_eq_zero_iff (y : Y) : (π f).hom y = 0 ↔ y ∈ LinearMap.range f.hom.toLinearMap :=
  Submodule.Quotient.mk_eq_zero _

noncomputable def seq : ShortComplex (Rep.{u} k G) where
  X₁ := X
  X₂ := Y
  X₃ := obj f
  f := f
  g := π f
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩))

end GroupCohomology.RepCokernel


