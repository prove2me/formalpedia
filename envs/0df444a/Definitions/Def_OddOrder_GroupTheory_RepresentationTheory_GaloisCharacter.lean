-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_GaloisCharacter
-- name    : OddOrder_GroupTheory_RepresentationTheory_GaloisCharacter
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:58:39.528072+00:00
-- url     : https://prove2.me/theorems/d82b855b-0b5b-4328-9fb6-a466cc5f451e
-- title:
--   Galois actions on class functions and irreducible characters
-- statement:
--   Coefficientwise automorphism infrastructure for class functions: a ring automorphism $\sigma$ of $\mathbb{C}$ sends a class function $\varphi$ to $g\mapsto\sigma(\varphi(g))$. The main theorem is that Galois conjugates of irreducible characters are irreducible, proved for every ring automorphism of $\mathbb{C}$ via the $\sigma$-twisted representation.
--
--   Main definitions: `mapRingEquiv` and `mapRingEquivLinear` (coefficientwise automorphism of class functions), `galoisCoord` (the $\sigma$-twisted coordinate bijection), `galoisTwist` (the $\sigma$-twist of a representation), `galoisMap` (the resulting irreducible character) and `galoisPerm` (Galois transport as a permutation of $\mathrm{Irr}(G)$).
--
--   The bundle also proves 33 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/GaloisCharacter.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/GaloisCharacter.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassFunction
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IrrIndexing
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible

namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {G : Type*} [Group G]

/-- Apply a ring automorphism of `ℂ` coefficientwise to a class function. -/
def mapRingEquiv (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) : ClassFunction G ℂ :=
  ⟨fun g => σ (φ g), by
    intro g h
    exact congrArg σ (φ.conj_eq g h)
  ⟩

@[simp] theorem mapRingEquiv_apply (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) (g : G) :
    mapRingEquiv σ φ g = σ (φ g) :=
  rfl

@[simp] theorem mapRingEquiv_zero (σ : ℂ ≃+* ℂ) :
    mapRingEquiv (G := G) σ 0 = 0 := by
  ext g
  simp [mapRingEquiv]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem mapRingEquiv_add (σ : ℂ ≃+* ℂ) (φ ψ : ClassFunction G ℂ) :
    mapRingEquiv σ (φ + ψ) = mapRingEquiv σ φ + mapRingEquiv σ ψ := by
  ext g
  simp [mapRingEquiv]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem mapRingEquiv_neg (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    mapRingEquiv σ (-φ) = -mapRingEquiv σ φ := by
  ext g
  simp [mapRingEquiv]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem mapRingEquiv_sub (σ : ℂ ≃+* ℂ) (φ ψ : ClassFunction G ℂ) :
    mapRingEquiv σ (φ - ψ) = mapRingEquiv σ φ - mapRingEquiv σ ψ := by
  ext g
  simp [mapRingEquiv]

@[simp] theorem zsmul_apply (n : ℤ) (φ : ClassFunction G ℂ) (g : G) :
    (n • φ) g = n • φ g := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem mapRingEquiv_zsmul (σ : ℂ ≃+* ℂ) (n : ℤ) (φ : ClassFunction G ℂ) :
    mapRingEquiv σ (n • φ) = n • mapRingEquiv σ φ := by
  ext g
  simp [mapRingEquiv]

/-- Coefficientwise automorphism as a `ℤ`-linear map of class functions. -/
def mapRingEquivLinear (σ : ℂ ≃+* ℂ) : (ClassFunction G ℂ →ₗ[ℤ] ClassFunction G ℂ) :=
  { toFun := mapRingEquiv σ
    map_add' := fun φ ψ => mapRingEquiv_add σ φ ψ
    map_smul' := fun n φ => mapRingEquiv_zsmul σ n φ }

@[simp] theorem mapRingEquivLinear_apply (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    mapRingEquivLinear (G := G) σ φ = mapRingEquiv σ φ :=
  rfl

@[simp] theorem mapRingEquiv_refl (φ : ClassFunction G ℂ) :
    mapRingEquiv (RingEquiv.refl ℂ) φ = φ := by
  ext g
  simp [mapRingEquiv]

@[simp] theorem mapRingEquiv_symm_mapRingEquiv (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    mapRingEquiv σ.symm (mapRingEquiv σ φ) = φ := by
  ext g
  simp [mapRingEquiv]

@[simp] theorem mapRingEquiv_mapRingEquiv_symm (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    mapRingEquiv σ (mapRingEquiv σ.symm φ) = φ := by
  ext g
  simp [mapRingEquiv]

@[simp] theorem mapRingEquiv_eq_zero_iff (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    mapRingEquiv σ φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    simpa using congrArg (mapRingEquiv σ.symm) h
  · intro h
    simp [h]

@[simp] theorem mapRingEquiv_ne_zero_iff (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    mapRingEquiv σ φ ≠ 0 ↔ φ ≠ 0 :=
  not_congr (mapRingEquiv_eq_zero_iff σ φ)

@[simp] theorem mem_support_mapRingEquiv (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) (g : G) :
    g ∈ (mapRingEquiv σ φ).support ↔ g ∈ φ.support := by
  simp [support, mapRingEquiv]

@[simp] theorem support_mapRingEquiv (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    (mapRingEquiv σ φ).support = φ.support := by
  ext g
  simp

end ClassFunction

section GaloisTwist

open Module (Basis)

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ι : Type*} [Fintype ι]

/-- The `σ`-twisted coordinate bijection attached to a basis `b` of `V`: send `v` to its
coordinate vector with `σ` applied entrywise.  It is additive and `σ`-semilinear
(`galoisCoord_smul`); we package only the additive bijection and carry the twisted scalar
action as a separate lemma, which is all the lattice transfer below needs. -/
noncomputable def galoisCoord (σ : ℂ ≃+* ℂ) (b : Basis ι ℂ V) : V ≃+ (ι → ℂ) where
  toFun v := fun i => σ (b.repr v i)
  invFun w := b.repr.symm (Finsupp.equivFunOnFinite.symm fun i => σ.symm (w i))
  left_inv v := by
    have h : (fun i => σ.symm (σ (b.repr v i))) = ⇑(b.repr v) := by
      funext i
      rw [RingEquiv.symm_apply_apply]
    change b.repr.symm (Finsupp.equivFunOnFinite.symm fun i => σ.symm (σ (b.repr v i))) = v
    rw [h, Finsupp.equivFunOnFinite_symm_coe]
    exact b.repr.symm_apply_apply v
  right_inv w := by
    funext i
    change σ (b.repr (b.repr.symm (Finsupp.equivFunOnFinite.symm fun i => σ.symm (w i))) i) = w i
    rw [LinearEquiv.apply_symm_apply]
    exact σ.apply_symm_apply (w i)
  map_add' v₁ v₂ := by
    funext i
    change σ (b.repr (v₁ + v₂) i) = σ (b.repr v₁ i) + σ (b.repr v₂ i)
    rw [map_add, Finsupp.add_apply, map_add]

@[simp] theorem galoisCoord_apply (σ : ℂ ≃+* ℂ) (b : Basis ι ℂ V) (v : V) (i : ι) :
    galoisCoord σ b v i = σ (b.repr v i) :=
  rfl

/-- `galoisCoord` is `σ`-semilinear. -/
theorem galoisCoord_smul (σ : ℂ ≃+* ℂ) (b : Basis ι ℂ V) (c : ℂ) (v : V) :
    galoisCoord σ b (c • v) = σ c • galoisCoord σ b v := by
  funext i
  rw [galoisCoord_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply,
    smul_eq_mul, galoisCoord_apply]

theorem galoisCoord_symm_smul (σ : ℂ ≃+* ℂ) (b : Basis ι ℂ V) (c : ℂ) (w : ι → ℂ) :
    (galoisCoord σ b).symm (c • w) = σ.symm c • (galoisCoord σ b).symm w := by
  apply (galoisCoord σ b).injective
  rw [AddEquiv.apply_symm_apply, galoisCoord_smul, RingEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

theorem galoisCoord_basis [DecidableEq ι] (σ : ℂ ≃+* ℂ) (b : Basis ι ℂ V) (j : ι) :
    galoisCoord σ b (b j) = Pi.single j 1 := by
  funext i
  rw [galoisCoord_apply, Basis.repr_self]
  rcases eq_or_ne i j with rfl | h
  · rw [Finsupp.single_eq_same, map_one, Pi.single_eq_same]
  · rw [Finsupp.single_eq_of_ne h, map_zero, Pi.single_eq_of_ne h]

theorem galoisCoord_symm_single [DecidableEq ι] (σ : ℂ ≃+* ℂ) (b : Basis ι ℂ V) (j : ι) :
    (galoisCoord σ b).symm (Pi.single j 1) = b j := by
  rw [AddEquiv.symm_apply_eq, galoisCoord_basis]

/-- The `σ`-twist of a representation `ρ : Representation ℂ G V`, realized on the coordinate
space `ι → ℂ` of a basis `b`: conjugate each `ρ g` by `galoisCoord σ b`.  The two coordinate
twists cancel the semilinearity, so each map is genuinely `ℂ`-linear. -/
noncomputable def galoisTwist (σ : ℂ ≃+* ℂ) (ρ : Representation ℂ G V) (b : Basis ι ℂ V) :
    Representation ℂ G (ι → ℂ) where
  toFun g :=
    { toFun := fun w => galoisCoord σ b (ρ g ((galoisCoord σ b).symm w))
      map_add' := fun w₁ w₂ => by rw [map_add, map_add, map_add]
      map_smul' := fun c w => by
        rw [RingHom.id_apply, galoisCoord_symm_smul, map_smul, galoisCoord_smul,
          RingEquiv.apply_symm_apply] }
  map_one' := by
    ext w
    simp
  map_mul' g h := by
    ext w
    simp [Module.End.mul_apply]

@[simp] theorem galoisTwist_apply (σ : ℂ ≃+* ℂ) (ρ : Representation ℂ G V)
    (b : Basis ι ℂ V) (g : G) (w : ι → ℂ) :
    galoisTwist σ ρ b g w = galoisCoord σ b (ρ g ((galoisCoord σ b).symm w)) :=
  rfl

theorem galoisTwist_apply_galoisCoord (σ : ℂ ≃+* ℂ) (ρ : Representation ℂ G V)
    (b : Basis ι ℂ V) (g : G) (v : V) :
    galoisTwist σ ρ b g (galoisCoord σ b v) = galoisCoord σ b (ρ g v) := by
  rw [galoisTwist_apply, AddEquiv.symm_apply_apply]

/-- The character of the `σ`-twist is the `σ`-image of the character: in the standard basis
of `ι → ℂ` the matrix of `galoisTwist σ ρ b g` is the entrywise `σ`-image of the matrix of
`ρ g` in the basis `b`. -/
theorem character_galoisTwist (σ : ℂ ≃+* ℂ) (ρ : Representation ℂ G V) (b : Basis ι ℂ V)
    (g : G) :
    (galoisTwist σ ρ b).character g = σ (ρ.character g) := by
  classical
  have hmat : LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) (galoisTwist σ ρ b g) =
      (LinearMap.toMatrix b b (ρ g)).map ⇑σ := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Matrix.map_apply, Pi.basisFun_repr, Pi.basisFun_apply,
      galoisTwist_apply, galoisCoord_symm_single, galoisCoord_apply]
  change LinearMap.trace ℂ (ι → ℂ) (galoisTwist σ ρ b g) = σ (LinearMap.trace ℂ V (ρ g))
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ ι), hmat,
    LinearMap.trace_eq_matrix_trace ℂ b, AddMonoidHom.map_trace]

/-- The `σ`-twist of an irreducible representation is irreducible: pulling a
subrepresentation of the twist back along `galoisCoord σ b` (an additive bijection that
intertwines the two actions and twists scalars by the bijection `σ`) yields a
subrepresentation of `ρ`. -/
theorem isIrreducible_galoisTwist (σ : ℂ ≃+* ℂ) {ρ : Representation ℂ G V}
    (b : Basis ι ℂ V) (hρ : ρ.IsIrreducible) : (galoisTwist σ ρ b).IsIrreducible := by
  have := hρ
  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have hbt : (⊥ : Submodule ℂ V) = ⊤ := by
      ext v
      simp [Subsingleton.elim v 0]
    exact bot_ne_top (α := Subrepresentation ρ)
      (Subrepresentation.toSubmodule_injective hbt)
  refine { toNontrivial := ?_, eq_bot_or_eq_top := fun S' => ?_ }
  · -- `⊥ ≠ ⊤` for subrepresentations of the twist, since `ι → ℂ` is nontrivial
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have hsub : (⊥ : Submodule ℂ (ι → ℂ)) = ⊤ := congrArg Subrepresentation.toSubmodule h
    obtain ⟨v, w, hvw⟩ := exists_pair_ne V
    refine hvw ((galoisCoord σ b).injective ?_)
    have hmem : ∀ u : ι → ℂ, u ∈ (⊥ : Submodule ℂ (ι → ℂ)) := fun u => by
      rw [hsub]; exact Submodule.mem_top
    have h₁ := Submodule.mem_bot ℂ |>.mp (hmem (galoisCoord σ b v))
    have h₂ := Submodule.mem_bot ℂ |>.mp (hmem (galoisCoord σ b w))
    rw [h₁, h₂]
  · -- pull `S'` back along `galoisCoord σ b` to a subrepresentation of `ρ`
    let p : Submodule ℂ V :=
      { carrier := {v : V | galoisCoord σ b v ∈ S'.toSubmodule}
        add_mem' := fun {v₁ v₂} h₁ h₂ => by
          change galoisCoord σ b (v₁ + v₂) ∈ S'.toSubmodule
          rw [map_add]
          exact S'.toSubmodule.add_mem h₁ h₂
        zero_mem' := by
          change galoisCoord σ b 0 ∈ S'.toSubmodule
          rw [map_zero]
          exact S'.toSubmodule.zero_mem
        smul_mem' := fun c v hv => by
          change galoisCoord σ b (c • v) ∈ S'.toSubmodule
          rw [galoisCoord_smul]
          exact S'.toSubmodule.smul_mem (σ c) hv }
    have hp : ∀ (g : G) ⦃v : V⦄, v ∈ p → ρ g v ∈ p := fun g v hv => by
      change galoisCoord σ b (ρ g v) ∈ S'.toSubmodule
      rw [← galoisTwist_apply_galoisCoord σ ρ b g v]
      exact S'.apply_mem_toSubmodule g hv
    rcases hρ.eq_bot_or_eq_top ⟨p, hp⟩ with h | h
    · left
      apply Subrepresentation.toSubmodule_injective
      have hp_bot : p = (⊥ : Submodule ℂ V) := congrArg Subrepresentation.toSubmodule h
      change S'.toSubmodule = (⊥ : Submodule ℂ (ι → ℂ))
      rw [Submodule.eq_bot_iff]
      intro w hw
      have hv : (galoisCoord σ b).symm w ∈ p := by
        change galoisCoord σ b ((galoisCoord σ b).symm w) ∈ S'.toSubmodule
        rw [AddEquiv.apply_symm_apply]
        exact hw
      rw [hp_bot, Submodule.mem_bot] at hv
      rw [← (galoisCoord σ b).apply_symm_apply w, hv, map_zero]
    · right
      apply Subrepresentation.toSubmodule_injective
      have hp_top : p = (⊤ : Submodule ℂ V) := congrArg Subrepresentation.toSubmodule h
      change S'.toSubmodule = (⊤ : Submodule ℂ (ι → ℂ))
      rw [Submodule.eq_top_iff']
      intro w
      have hv : (galoisCoord σ b).symm w ∈ p := by
        rw [hp_top]
        exact Submodule.mem_top
      have hw : galoisCoord σ b ((galoisCoord σ b).symm w) ∈ S'.toSubmodule := hv
      rwa [AddEquiv.apply_symm_apply] at hw

/-- **Galois conjugates of irreducible characters are irreducible.**  For any ring
automorphism `σ : ℂ ≃+* ℂ` and any irreducible character `φ` of `G`, the coefficientwise
transport `g ↦ σ (φ g)` is again an irreducible character: the witnessing representation is
the `σ`-twist `galoisTwist σ ρ b` of a witness `ρ` for `φ`. -/
theorem IsIrreducibleCharacter.mapRingEquiv {φ : ClassFunction G ℂ} (σ : ℂ ≃+* ℂ)
    (hφ : IsIrreducibleCharacter φ) :
    IsIrreducibleCharacter (ClassFunction.mapRingEquiv σ φ) := by
  classical
  obtain ⟨W, _, _, _, ρ, hirr, hchar⟩ := hφ
  let b := Module.Free.chooseBasis ℂ W
  refine ⟨Module.Free.ChooseBasisIndex ℂ W → ℂ, inferInstance, inferInstance, inferInstance,
    galoisTwist σ ρ b, isIrreducible_galoisTwist σ b hirr, ?_⟩
  funext g
  change σ (φ g) = (galoisTwist σ ρ b).character g
  rw [character_galoisTwist]
  exact congrArg σ (congrFun hchar g)

end GaloisTwist

namespace IrreducibleCharacter

variable {G : Type*} [Group G]

/-- The irreducible character obtained by coefficientwise Galois transport. -/
noncomputable def galoisMap (σ : ℂ ≃+* ℂ) (χ : IrreducibleCharacter G) :
    IrreducibleCharacter G :=
  ⟨ClassFunction.mapRingEquiv σ (χ : ClassFunction G ℂ),
    IsIrreducibleCharacter.mapRingEquiv σ χ.2⟩

@[simp] theorem galoisMap_apply_coe (σ : ℂ ≃+* ℂ) (χ : IrreducibleCharacter G) :
    ((galoisMap σ χ : IrreducibleCharacter G) : ClassFunction G ℂ) =
      ClassFunction.mapRingEquiv σ (χ : ClassFunction G ℂ) :=
  rfl

@[simp] theorem galoisMap_apply_apply (σ : ℂ ≃+* ℂ) (χ : IrreducibleCharacter G) (g : G) :
    ((galoisMap σ χ : IrreducibleCharacter G) : ClassFunction G ℂ) g =
      σ ((χ : ClassFunction G ℂ) g) :=
  rfl

@[simp] theorem galoisMap_refl (χ : IrreducibleCharacter G) :
    galoisMap (RingEquiv.refl ℂ) χ = χ := by
  apply IrreducibleCharacter.ext
  simp [galoisMap]

@[simp] theorem galoisMap_symm_galoisMap (σ : ℂ ≃+* ℂ) (χ : IrreducibleCharacter G) :
    galoisMap σ.symm (galoisMap σ χ) = χ := by
  apply IrreducibleCharacter.ext
  simp [galoisMap]

@[simp] theorem galoisMap_galoisMap_symm (σ : ℂ ≃+* ℂ) (χ : IrreducibleCharacter G) :
    galoisMap σ (galoisMap σ.symm χ) = χ := by
  apply IrreducibleCharacter.ext
  simp [galoisMap]

/-- Coefficientwise Galois transport as a permutation of `Irr(G)`. -/
noncomputable def galoisPerm (σ : ℂ ≃+* ℂ) : Equiv.Perm (IrreducibleCharacter G) where
  toFun := galoisMap σ
  invFun := galoisMap σ.symm
  left_inv := galoisMap_symm_galoisMap σ
  right_inv := galoisMap_galoisMap_symm σ

@[simp] theorem galoisPerm_apply (σ : ℂ ≃+* ℂ) (χ : IrreducibleCharacter G) :
    galoisPerm σ χ = galoisMap σ χ :=
  rfl

@[simp] theorem galoisPerm_apply_coe (σ : ℂ ≃+* ℂ) (χ : IrreducibleCharacter G) :
    ((galoisPerm σ χ : IrreducibleCharacter G) : ClassFunction G ℂ) =
      ClassFunction.mapRingEquiv σ (χ : ClassFunction G ℂ) :=
  rfl

@[simp] theorem galoisPerm_apply_apply (σ : ℂ ≃+* ℂ) (χ : IrreducibleCharacter G) (g : G) :
    ((galoisPerm σ χ : IrreducibleCharacter G) : ClassFunction G ℂ) g =
      σ ((χ : ClassFunction G ℂ) g) :=
  rfl

@[simp] theorem galoisPerm_refl :
    galoisPerm (G := G) (RingEquiv.refl ℂ) = Equiv.refl (IrreducibleCharacter G) := by
  ext χ g
  simp [galoisPerm, galoisMap]

end IrreducibleCharacter

namespace ClassFunction

variable {G : Type*} [Group G]

/-- A coefficientwise automorphism sends `Irr(G)` into `Irr(G)`. -/
theorem mapRingEquiv_mem_irreducibleCharacters (σ : ℂ ≃+* ℂ)
    {φ : ClassFunction G ℂ} (hφ : φ ∈ irreducibleCharacters G) :
    mapRingEquiv σ φ ∈ irreducibleCharacters G :=
  IsIrreducibleCharacter.mapRingEquiv σ hφ

/-- A coefficientwise automorphism permutes `Irr(G)`. -/
@[simp] theorem mapRingEquiv_image_irreducibleCharacters (σ : ℂ ≃+* ℂ) :
    mapRingEquiv σ '' irreducibleCharacters G = irreducibleCharacters G := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact mapRingEquiv_mem_irreducibleCharacters σ hψ
  · intro hφ
    exact ⟨mapRingEquiv σ.symm φ, mapRingEquiv_mem_irreducibleCharacters σ.symm hφ,
      mapRingEquiv_mapRingEquiv_symm σ φ⟩

/-- A coefficientwise automorphism preserves the virtual character lattice `ℤ[Irr G]`. -/
theorem mapRingEquiv_mem_ZIrr (σ : ℂ ≃+* ℂ)
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) :
    mapRingEquiv σ φ ∈ ZIrr G := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      exact IsIrreducibleCharacter.mem_ZIrr
        (mapRingEquiv_mem_irreducibleCharacters σ hx)
  | zero =>
      rw [mapRingEquiv_zero]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [mapRingEquiv_add]
      exact Submodule.add_mem _ hx hy
  | smul n x _ hx =>
      rw [mapRingEquiv_zsmul]
      exact Submodule.smul_mem _ n hx

end ClassFunction

end OddOrder.RepresentationTheory


