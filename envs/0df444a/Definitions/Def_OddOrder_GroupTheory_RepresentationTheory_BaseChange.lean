-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BaseChange
-- name    : OddOrder_GroupTheory_RepresentationTheory_BaseChange
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:20.560663+00:00
-- url     : https://prove2.me/theorems/a1467610-f529-481b-ba67-be66306ea80a
-- title:
--   Scalar extension (base change) of group representations
-- statement:
--   Extends a representation $\rho:G\to GL(V)$ over a field $F$ along a field extension $K/F$ to a representation on $K\otimes_F V$. This is the bridge used in Bender–Glauberman §2/§3 (and Thm 2.6(b)) to reduce a representation over an arbitrary field to one over its algebraic closure, as in the opening of the proof of Thm 2.5.
--
--   Main definitions: `baseChangeRepresentation` (scalar extension of a representation), `frobeniusScalarBaseChange` (absolute Frobenius on the scalar factor of a base change), and `invariantsObstruction` (the map $v\mapsto(g\mapsto\rho(g)v-v)$ whose kernel is the space of invariants), together with a helper for base change of mixed bilinear maps.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/BaseChange.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/BaseChange.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.Dimension.Constructions

open scoped TensorProduct

namespace LinearMap

universe uMixedR uMixedA uMixedM uMixedN uMixedP

variable {R : Type uMixedR} {A : Type uMixedA}

variable {M : Type uMixedM} {N : Type uMixedN} {P : Type uMixedP}

variable [CommSemiring R] [CommSemiring A] [Algebra R A]

variable [AddCommMonoid M] [Module R M]

variable [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module R P]

variable (A) in
/-- Extend scalars in both inputs and the output of a mixed bilinear map.

Unlike `LinearMap.BilinMap.baseChange`, the two input modules may differ. -/
def baseChange₂ (b : M →ₗ[R] N →ₗ[R] P) :
    (A ⊗[R] M) →ₗ[A] (A ⊗[R] N) →ₗ[A] (A ⊗[R] P) :=
  (TensorProduct.lift.equiv (.id A)
      (A ⊗[R] M) (A ⊗[R] N) (A ⊗[R] P)).symm
    ((TensorProduct.lift b).baseChange A ∘ₗ
      (TensorProduct.AlgebraTensorModule.distribBaseChange
        R A M N).symm.toLinearMap)

/-- Evaluation of `baseChange₂` on pure tensors. -/
@[simp]
theorem baseChange₂_tmul (b : M →ₗ[R] N →ₗ[R] P)
    (a c : A) (m : M) (n : N) :
    b.baseChange₂ A (a ⊗ₜ[R] m) (c ⊗ₜ[R] n) =
      (a * c) ⊗ₜ[R] b m n := by
  simp [baseChange₂]

end LinearMap

namespace OddOrder.RepresentationTheory

universe uFrobeniusL uFrobeniusV uFrobeniusW

/-- Absolute Frobenius on the scalar factor of an `F₂` base change. -/
noncomputable def frobeniusScalarBaseChange
    (L : Type uFrobeniusL) [Field L] [Finite L] [Algebra (ZMod 2) L]
    {V : Type uFrobeniusV} [AddCommMonoid V] [Module (ZMod 2) V] :
    (L ⊗[ZMod 2] V) →ₗ[ZMod 2] (L ⊗[ZMod 2] V) := by
  letI : Fintype L := Fintype.ofFinite L
  exact TensorProduct.map
    (FiniteField.frobeniusAlgHom (ZMod 2) L).toLinearMap
    (LinearMap.id : V →ₗ[ZMod 2] V)

@[simp]
theorem frobeniusScalarBaseChange_tmul
    (L : Type uFrobeniusL) [Field L] [Finite L] [Algebra (ZMod 2) L]
    {V : Type uFrobeniusV} [AddCommMonoid V] [Module (ZMod 2) V]
    (a : L) (v : V) :
    frobeniusScalarBaseChange L (a ⊗ₜ[ZMod 2] v) =
      (a ^ 2) ⊗ₜ[ZMod 2] v := by
  simp [frobeniusScalarBaseChange]

/-- Scalar extension of a representation along a field extension.

The concrete base-change object `Representation K G (K ⊗[F] V)`: `g` acts by `id_K ⊗ ρ g`. -/
noncomputable def baseChangeRepresentation
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Type*) [Field K] [Algebra F K]
    (ρ : Representation F G V) :
    Representation K G (TensorProduct F K V) where
  toFun g := TensorProduct.AlgebraTensorModule.map (R := F) (A := K)
    (M := K) (N := V) (P := K) (Q := V)
    (LinearMap.id : K →ₗ[K] K) (ρ g)
  map_one' := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a v
    simp
  map_mul' g h := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a v
    simp [map_mul]

/-- `baseChangeRepresentation` の単純テンソル上の作用: `a ⊗ₜ v ↦ a ⊗ₜ ρ g v`. -/
@[simp]
theorem baseChangeRepresentation_apply_tmul
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Type*) [Field K] [Algebra F K]
    (ρ : Representation F G V) (g : G) (a : K) (v : V) :
    baseChangeRepresentation K ρ g (a ⊗ₜ[F] v) = a ⊗ₜ[F] ρ g v := by
  simp [baseChangeRepresentation]

/-- Faithfulness survives scalar extension along a faithfully flat field extension.

For the algebraic-closure route, `K` will be `AlgebraicClosure F`.  The proof uses the canonical
injection `V → K ⊗[F] V`. -/
theorem baseChangeRepresentation_faithful
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Type*) [Field K] [Algebra F K] [Module.FaithfullyFlat F K]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ) :
    Function.Injective (baseChangeRepresentation K ρ) := by
  intro g h hgh
  apply hfaithful
  ext v
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := F) (B := K) V
  have hmap := congrArg
    (fun f : TensorProduct F K V →ₗ[K] TensorProduct F K V => f (1 ⊗ₜ[F] v)) hgh
  simpa [baseChangeRepresentation] using hmap

/-- The obstruction map `v ↦ (g ↦ ρ g v - v)`; its kernel is the space of invariants. -/
private noncomputable def invariantsObstruction
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) :
    V →ₗ[F] (G → V) :=
  LinearMap.pi (fun g => ρ g - LinearMap.id)

private theorem ker_invariantsObstruction
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) :
    LinearMap.ker (invariantsObstruction ρ) = Representation.invariants ρ := by
  ext v
  rw [LinearMap.mem_ker, Representation.mem_invariants, funext_iff]
  refine forall_congr' (fun g => ?_)
  simp [invariantsObstruction, LinearMap.pi_apply, LinearMap.sub_apply, sub_eq_zero]

/-- **Base change preserves vanishing of invariants**: if a representation `ρ` over a field `F`
has no nonzero invariants, then neither does its scalar extension to any field extension `K/F`.

This is the field-agnostic bridge that transfers a hypothesis `C_V(R) = 0` to the algebraic
closure (BG §2/§3): apply it to the restricted representation `ρ.comp R.subtype`.  The proof
factors the invariants as `ker` of the obstruction map `v ↦ (g ↦ ρ g v - v)`; flatness of `K`
over `F` preserves the injectivity of that map, and `TensorProduct.piRight` identifies its scalar
extension with the obstruction map of the base-changed representation. -/
theorem invariants_baseChangeRepresentation_eq_bot
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Type*) [Field K] [Algebra F K]
    (ρ : Representation F G V) (h : Representation.invariants ρ = ⊥) :
    Representation.invariants (baseChangeRepresentation K ρ) = ⊥ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set ρ' := baseChangeRepresentation K ρ with hρ'
  -- `ρ`'s obstruction map is injective (its kernel is the invariants, which vanish).
  have hinj : Function.Injective (invariantsObstruction ρ) := by
    rw [← LinearMap.ker_eq_bot, ker_invariantsObstruction, h]
  -- flatness of `K/F` preserves injectivity under `lTensor`.
  have hlt : Function.Injective (LinearMap.lTensor K (invariantsObstruction ρ)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  -- `piRight ∘ lTensor` agrees with `ρ'`'s obstruction map on the nose.
  have hcompat : ∀ x : TensorProduct F K V,
      invariantsObstruction ρ' x
        = TensorProduct.piRight F K K (fun _ : G => V)
            (LinearMap.lTensor K (invariantsObstruction ρ) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        funext g
        simp [invariantsObstruction, hρ', LinearMap.pi_apply, LinearMap.sub_apply,
          baseChangeRepresentation_apply_tmul, LinearMap.lTensor_tmul,
          TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => simp [map_add, hx, hy]
  -- hence `ρ'`'s obstruction map is injective, so its invariants vanish.
  have hinj' : Function.Injective (invariantsObstruction ρ') := by
    have hfun : (invariantsObstruction ρ' : TensorProduct F K V → (G → TensorProduct F K V))
        = (TensorProduct.piRight F K K (fun _ : G => V)) ∘
            (LinearMap.lTensor K (invariantsObstruction ρ)) := funext hcompat
    rw [show ⇑(invariantsObstruction ρ') = _ from hfun]
    exact (TensorProduct.piRight F K K (fun _ : G => V)).injective.comp hlt
  rw [← ker_invariantsObstruction ρ', LinearMap.ker_eq_bot.mpr hinj']

/-- **Base change preserves the dimension of the invariants** (BG (2.9), dimension form).  For a
finite group `G` and a field extension `K/F`, the `K`-dimension of `C_{K⊗V}(G)` equals the
`F`-dimension of `C_V(G)`.

The space of invariants is the kernel of the obstruction map `f : v ↦ (g ↦ ρ g v - v)`; the
obstruction map of the base-changed representation factors as `piRight ∘ (K ⊗ f)`, so its kernel
(over `K`) equals `ker (K ⊗ f)`.  Flatness of `K/F` (`Module.Flat.ker_lTensor_eq`) identifies that
kernel with `K ⊗ ker f`, whose `K`-dimension is `finrank F (ker f) = finrank F C_V(G)`
(`Module.finrank_baseChange`).

Applied to `ρ.comp R.subtype` this transfers `dim C_V(R) = 1` to the algebraic closure, the
hypothesis form needed by BG Theorem 3.5. -/
theorem finrank_invariants_baseChangeRepresentation
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (K : Type*) [Field K] [Algebra F K]
    (ρ : Representation F G V) :
    Module.finrank K (Representation.invariants (baseChangeRepresentation K ρ))
      = Module.finrank F (Representation.invariants ρ) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set f := invariantsObstruction ρ with hf
  set e := TensorProduct.piRight F K K (fun _ : G => V) with he
  -- the `K`-linear obstruction map of `baseChange ρ` factors as `e ∘ (K ⊗ f)`.
  have hfactor : invariantsObstruction (baseChangeRepresentation K ρ)
      = e.toLinearMap ∘ₗ TensorProduct.AlgebraTensorModule.lTensor K K f := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        funext g
        simp only [hf, he, invariantsObstruction, LinearMap.pi_apply, LinearMap.sub_apply,
          LinearMap.id_coe, id_eq, baseChangeRepresentation_apply_tmul, LinearMap.comp_apply,
          TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearEquiv.coe_coe,
          TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  -- kernels agree (`e` is an isomorphism).
  have hkere : LinearMap.ker e.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr e.injective
  have hker : LinearMap.ker (invariantsObstruction (baseChangeRepresentation K ρ))
      = LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor K K f) := by
    rw [hfactor, LinearMap.ker_comp, hkere, Submodule.comap_bot]
  -- `K ⊗ (subtype of ker f)` is injective (flatness), so its range has dimension
  -- `finrank F (ker f)`.
  have hinj : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor K K
      (LinearMap.ker f).subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (LinearMap.ker f).subtype (Submodule.injective_subtype _)
  rw [← ker_invariantsObstruction (baseChangeRepresentation K ρ), hker,
    Module.Flat.ker_lTensor_eq K K f, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_baseChange, hf, ker_invariantsObstruction]

/-- Base change commutes with restriction along a group hom `φ : H →* G`.

Lets the whole-group transfer lemmas apply to a subgroup: with `φ = H.subtype` and `ρ.comp φ`
the restricted representation, `C_V(H) = ⊥` over `F` transfers to `C_{K⊗V}(H) = ⊥` over `K`
(this is the form of BG (2.9), used at `H = Z(P)`). -/
@[simp]
theorem baseChangeRepresentation_comp
    {F : Type*} [Field F] {G H : Type*} [Group G] [Group H]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Type*) [Field K] [Algebra F K]
    (ρ : Representation F G V) (φ : H →* G) :
    baseChangeRepresentation K (ρ.comp φ) = (baseChangeRepresentation K ρ).comp φ := rfl

end OddOrder.RepresentationTheory


