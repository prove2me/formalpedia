-- Prove2me | Definitions.Def_JacJ1Iface
-- name    : JacJ1Iface
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/90cccceb-8f31-521e-a538-22a1cc17c247
-- title:
--   Carriers for Jacobian data and relative group laws over a base
-- statement:
--   Four carriers are set up. For a commutative ring $R$ and a morphism $f \colon A \to \operatorname{Spec} R$, `AbelianSchemePropertyBundle` is a `Prop`-valued structure with four fields: $f$ is smooth, $f$ is proper, for every point $s$ of the underlying space of $\operatorname{Spec} R$ the fibre $f^{-1}(\{s\})$ of the underlying continuous map is connected (in Mathlib's `IsConnected` sense, so in particular nonempty), and the type `RelativeGroupLaw R f` is nonempty, i.e. the functor of points $t \mapsto \{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ carries a group law with multiplication, unit and inverse satisfying the group axioms pointwise and with multiplication natural in the test object. `RelativePic0Designation R c`, indexed by a morphism $c \colon C \to \operatorname{Spec} R$, is pure data: a scheme $P$, a structure morphism `toBase` $\colon P \to \operatorname{Spec} R$ and a section `zeroSection` of it. No compatibility between $P$ and $C$ is imposed; $c$ enters only as an index, so the designation records a chosen candidate for $\operatorname{Pic}^0_{C/R}$ rather than constructing it. `trivialPic0Designation` designates $\operatorname{Spec} R$ with identity morphisms. `AvatarSchemeBridge A D L σ` links an abstract additive group $A$ to such a designation: a bijection `pts` from $A$ onto the $\sigma$-points of `D.toBase` which turns addition into the group law $L$ and sends $0$ to $\sigma$ followed by the zero section. The lemma `law_one_eq_pts_zero` derives from the group axioms that the unit of $L$ at $\sigma$ equals `pts 0`, using only idempotence of `pts 0`.
--
--   Over a field $k$, `JacobianSchemeData A c g σ` bundles a designation, a group law on it, a bridge for $A$, an `AbelianSchemePropertyBundle` for `D.toBase`, and a field `hDim : Prop` which is an arbitrary proposition, carrying no condition relating $g$ to the designation. The assembler `JacobianSchemeData.ofCore` produces such data at $\sigma = \mathrm{id}$ from a scheme $J$ with structure morphism $f$, a group law, an additive bijection $A \simeq$ (sections of $f$), and smoothness, properness and connectedness of fibres, taking the zero section to be the section underlying `pts 0` and `hDim` to be `True`.
--
--   **Relation to Mathlib.** Smoothness, properness and connectedness are Mathlib's `Smooth`, `IsProper` and `IsConnected`; Mathlib has no notion of abelian scheme, relative $\operatorname{Pic}^0$ or relative group law on a functor of points, so these carriers, together with `SchemeHomOver` and `RelativeGroupLaw` from the imported modules, are the project's own.
--
--   **Where it is used.** These carriers provide the interface through which Jacobians of curves (in particular of modular curves) are treated as abelian schemes with a group law on their points, feeding the Néron-model and good-reduction infrastructure used for the Galois representations in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_JacJ1Iface.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

open NeronModelInfra

namespace GoodReductionJacobian

section AbstractCarriers

variable (R : Type u) [CommRing R]

structure AbelianSchemePropertyBundle {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) :
    Prop where

  smooth : Smooth f

  proper : IsProper f

  connectedFibres : ∀ s : Spec (CommRingCat.of R), _root_.IsConnected (f.base ⁻¹' {s})

  hasGroupLaw : Nonempty (RelativeGroupLaw R f)

structure RelativePic0Designation {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) where

  P : Scheme.{u}

  toBase : P ⟶ Spec (CommRingCat.of R)

  zeroSection : Spec (CommRingCat.of R) ⟶ P

  zeroSection_toBase : zeroSection ≫ toBase = 𝟙 (Spec (CommRingCat.of R))

def trivialPic0Designation {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) :
    RelativePic0Designation R c where
  P := Spec (CommRingCat.of R)
  toBase := 𝟙 _
  zeroSection := 𝟙 _
  zeroSection_toBase := Category.comp_id _

end AbstractCarriers

section AvatarBridge

variable {R : Type u} [CommRing R]
variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

structure AvatarSchemeBridge (A : Type*) [AddCommGroup A]
    (D : RelativePic0Designation R c) (L : RelativeGroupLaw R D.toBase)
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of R)) where

  pts : A ≃ SchemeHomOver σ D.toBase

  pts_add : ∀ x y : A, pts (x + y) = L.mul σ (pts x) (pts y)

  pts_zero : (pts 0).1 = σ ≫ D.zeroSection

namespace AvatarSchemeBridge

variable {A : Type*} [AddCommGroup A]
variable {D : RelativePic0Designation R c} {L : RelativeGroupLaw R D.toBase}
variable {T : Scheme.{u}} {σ : T ⟶ Spec (CommRingCat.of R)}

theorem law_one_eq_pts_zero (B : AvatarSchemeBridge A D L σ) :
    L.one σ = B.pts 0 := by
  have hidem : L.mul σ (B.pts 0) (B.pts 0) = B.pts 0 := by
    rw [← B.pts_add, add_zero]
  calc L.one σ
      = L.mul σ (L.inv σ (B.pts 0)) (B.pts 0) := (L.inv_mul_cancel σ (B.pts 0)).symm
    _ = L.mul σ (L.inv σ (B.pts 0)) (L.mul σ (B.pts 0) (B.pts 0)) := by rw [hidem]
    _ = L.mul σ (L.mul σ (L.inv σ (B.pts 0)) (B.pts 0)) (B.pts 0) :=
        (L.mul_assoc σ _ _ _).symm
    _ = L.mul σ (L.one σ) (B.pts 0) := by rw [L.inv_mul_cancel]
    _ = B.pts 0 := L.one_mul σ _

end AvatarSchemeBridge

end AvatarBridge

end GoodReductionJacobian

namespace MilneJVScheme

open GoodReductionJacobian

variable {k : Type u} [Field k]

structure JacobianSchemeData (A : Type*) [AddCommGroup A]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (g : ℕ)
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of k)) where

  D : RelativePic0Designation k c

  L : RelativeGroupLaw k D.toBase

  bridge : AvatarSchemeBridge A D L σ

  hAbel : AbelianSchemePropertyBundle k D.toBase

  hDim : Prop

def JacobianSchemeData.ofCore (A : Type*) [AddCommGroup A]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (g : ℕ)
    {J : Scheme.{u}} (f : J ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    (pts : A ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (pts_add : ∀ x y : A, pts (x + y) = L.mul (𝟙 (Spec (CommRingCat.of k))) (pts x) (pts y))
    (hsmooth : Smooth f) (hproper : IsProper f)
    (hconn : ∀ s : Spec (CommRingCat.of k), _root_.IsConnected (f.base ⁻¹' {s})) :
    JacobianSchemeData A c g (𝟙 (Spec (CommRingCat.of k))) where
  D :=
    { P := J
      toBase := f
      zeroSection := (pts 0).1
      zeroSection_toBase := (pts 0).2 }
  L := L
  bridge :=
    { pts := pts
      pts_add := pts_add
      pts_zero := (Category.id_comp _).symm }
  hAbel :=
    { smooth := hsmooth
      proper := hproper
      connectedFibres := hconn
      hasGroupLaw := ⟨L⟩ }
  hDim := True

end MilneJVScheme


