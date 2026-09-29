-- Prove2me | Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
-- name    : AlgebraicGeometry_SmallExtensionTangentCoords
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/5a9b5724-4d20-5038-ab5e-8921f39443bb
-- title:
--   Tangent coordinates for maps into a first-order thickening
-- statement:
--   Throughout, $T'$ is a local ring with residue field $k =$ `ResidueField T'`, $V$ is a $k$-module which is simultaneously a module over $k^{\mathrm{op}}$ with the two actions agreeing (a central bimodule), and $C$ is a commutative $T'$-algebra. The ring `thickening T' V C` of the pair-tangent setting is $(k \otimes_{T'} C) \otimes_k (k \oplus V)$, where $k \oplus V$ is the trivial square-zero extension `TrivSqZeroExt k V`; writing $C_k = k \otimes_{T'} C$, it is the coordinate ring of the first-order thickening of $\operatorname{Spec} C_k$ in the direction $V$. Three definitions are made. First, `vPart` is the $k$-linear projection $C_k \otimes_k (k \oplus V) \to C_k \otimes_k V$ obtained by tensoring the identity of $C_k$ with the second-coordinate map $k \oplus V \to V$, i.e. extraction of the "$\varepsilon$-part". Second, for a field $k$ and $k$-modules $M$, $W$, `tensorToDualHom` is the canonical $k$-linear map $M \otimes_k W \to \operatorname{Hom}_k(W^{\vee}, M)$ determined by $m \otimes w \mapsto (\xi \mapsto \xi(w)\, m)$, whose value on pure tensors is recorded as a simp lemma. Third, for an arbitrary commutative ring $A$ and an arbitrary ring homomorphism $\varphi \colon A \to$ `thickening T' V C`, `tangentCoords` assigns to each $a \in A$ the element
--   $$\operatorname{tangentCoords}(\varphi)(a) = \bigl(\xi \mapsto (\mathrm{id} \otimes \xi)(\text{$V$-part of } \varphi(a))\bigr) \in \operatorname{Hom}_k(V^{\vee}, C_k),$$
--   the composite of `vPart` with `tensorToDualHom`. This is defined as a bare function of $a$, with no hypothesis relating $\varphi$ to a $k$-point; its additivity in $a$ is recorded separately (`tangentCoords_add`), together with an unfolding lemma. No choice of basis of $V$ or of cotangent representatives enters: the coordinates are attached directly to $\varphi$.
--
--   **Relation to Mathlib.** Built from Mathlib's `TrivSqZeroExt`, `Module.Dual` and tensor-product machinery; the resulting value-level tangent coordinates of a ring map into a thickening are the project's own notion.
--
--   **Where it is used.** These coordinates give a basis-free, value-level record of the $V$-direction of a map into the thickening $\operatorname{Spec}\bigl((k \otimes_{T'} C) \otimes_k (k \oplus V)\bigr)$, so that statements asserting linearity or cocycle identities for tangent data (re-gluing, injectivity modulo coboundaries, Kodaira–Spencer type linearity) can be formulated against a fixed function rather than an existentially quantified identification. They are used together with the pair-tangent predicates `IsSchlessingerMap` and `IsTangentOfPair` in the infinitesimal, deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SmallExtensionTangentCoords.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 100000

noncomputable section

universe u

open TensorProduct IsLocalRing

namespace AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]

variable (T') in

def vPart : thickening T' V C →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V :=
  TensorProduct.map LinearMap.id (TrivSqZeroExt.sndHom (ResidueField T') V)

def tensorToDualHom (k : Type u) [Field k] (M : Type u) [AddCommGroup M] [Module k M]
    (W : Type u) [AddCommGroup W] [Module k W] :
    M ⊗[k] W →ₗ[k] (Module.Dual k W →ₗ[k] M) :=
  TensorProduct.lift
    (LinearMap.mk₂ k (fun (m : M) (w : W) => (LinearMap.smulRight (Module.Dual.eval k W w) m : Module.Dual k W →ₗ[k] M))
      (fun m₁ m₂ w => by ext ξ; simp)
      (fun c m w => by ext ξ; simp [smul_smul, mul_comm])
      (fun m w₁ w₂ => by ext ξ; simp [add_smul])
      (fun c m w => by ext ξ; simp [smul_smul]))

@[simp] theorem tensorToDualHom_tmul (k : Type u) [Field k] (M : Type u) [AddCommGroup M] [Module k M]
    (W : Type u) [AddCommGroup W] [Module k W] (m : M) (w : W) (ξ : Module.Dual k W) :
    tensorToDualHom k M W (m ⊗ₜ w) ξ = ξ w • m := by
  simp [tensorToDualHom]

variable (T') in

def tangentCoords {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a : A) :
    Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C) :=
  tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C) V (vPart T' V C (φ a))

theorem tangentCoords_apply {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a : A) (ξ : Module.Dual (ResidueField T') V) :
    tangentCoords T' V C φ a ξ = tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C) V (vPart T' V C (φ a)) ξ := rfl

theorem tangentCoords_add {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a b : A) :
    tangentCoords T' V C φ (a + b) = tangentCoords T' V C φ a + tangentCoords T' V C φ b := by
  unfold tangentCoords
  rw [φ.map_add, LinearMap.map_add, LinearMap.map_add]

end AlgebraicGeometry.SmallExtension

end


