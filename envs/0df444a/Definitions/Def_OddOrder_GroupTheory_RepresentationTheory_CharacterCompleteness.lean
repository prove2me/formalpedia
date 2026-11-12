-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
-- name    : OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:03:03.939061+00:00
-- url     : https://prove2.me/theorems/256260b8-7ef5-4578-9792-c1db7bdf3e13
-- title:
--   Completeness of irreducible characters (toward $|\mathrm{Irr}\,G|=|\mathrm{ConjClasses}\,G|$)
-- statement:
--   Work toward showing that the irreducible characters span the space of class functions. The strategy attaches to a class function $f$ and a representation $\rho$ the operator $T_\rho f=\sum_g f(g)\rho(g)$, which is an intertwiner because $f$ is a class function; by Schur's lemma it is a scalar on an irreducible representation. The module also proves that the character of any finite-dimensional complex representation lies in $\mathbb{Z}[\mathrm{Irr}\,G]$ (`character_mem_ZIrr`).
--
--   Main definitions: `classFunctionOperator` and `classFunctionIntertwiner` (the operator $T_\rho f$), `transportRep` (transport of a representation along a linear equivalence), `classFunctionInv`, `ofSubmodulePrimeAsModuleEquiv`, `innerAgainstIrreducibleCharacters`, and character-table indexing data `CharacterTableIndexing.ofFinite'`.
--
--   The bundle also proves 16 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CharacterCompleteness.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CharacterCompleteness.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCount
import Definitions.Def_OddOrder_Mathlib_MonoidAlgebra
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

namespace OddOrder.RepresentationTheory

open Module (finrank)

section CFOp

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]

/-- The operator `∑_{g ∈ G} f(g) • ρ(g)` attached to a class function `f` and a
representation `ρ`, as an endomorphism of `V`. -/
noncomputable def classFunctionOperator (f : ClassFunction G ℂ) (ρ : Representation ℂ G V) :
    Module.End ℂ V :=
  ∑ g : G, f g • ρ g

/-- The class-function operator commutes with the representation: `ρ(h) ∘ T = T ∘ ρ(h)`.
This is the `G`-intertwiner property, and it holds precisely because `f` is constant on
conjugacy classes. -/
theorem classFunctionOperator_comm (f : ClassFunction G ℂ) (ρ : Representation ℂ G V) (h : G) :
    ρ h * classFunctionOperator f ρ = classFunctionOperator f ρ * ρ h := by
  unfold classFunctionOperator
  rw [Finset.mul_sum, Finset.sum_mul]
  -- LHS term: ρ h * (f g • ρ g) = f g • ρ (h * g); RHS term: (f g • ρ g) * ρ h = f g • ρ (g * h)
  have hL : ∀ g : G, ρ h * (f g • ρ g) = f g • ρ (h * g) := by
    intro g; rw [mul_smul_comm, ← map_mul]
  have hR : ∀ g : G, (f g • ρ g) * ρ h = f g • ρ (g * h) := by
    intro g; rw [smul_mul_assoc, ← map_mul]
  rw [Finset.sum_congr rfl (fun g _ => hL g), Finset.sum_congr rfl (fun g _ => hR g)]
  -- Goal: ∑ g, f g • ρ (h * g) = ∑ g, f g • ρ (g * h).
  -- Reindex the RHS by conjugation `g ↦ h * g * h⁻¹`, which sends `g * h ↦ h * g` and fixes `f`.
  rw [← Equiv.sum_comp (MulAut.conj h).toEquiv (fun g => f g • ρ (g * h))]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  have hconj : (MulAut.conj h).toEquiv g = h * g * h⁻¹ := by simp [MulAut.conj_apply]
  rw [hconj, f.conj_eq g h, show h * g * h⁻¹ * h = h * g from by group]

/-- The class-function operator `T_ρ f`, packaged as an `IntertwiningMap ρ ρ`
(`classFunctionOperator_comm` is exactly the intertwining condition). -/
noncomputable def classFunctionIntertwiner (f : ClassFunction G ℂ) (ρ : Representation ℂ G V) :
    Representation.IntertwiningMap ρ ρ :=
  (classFunctionOperator f ρ).intertwiningMap_of_isIntertwiningMap ρ ρ (by
    intro g v
    have h := classFunctionOperator_comm f ρ g
    have h2 := (LinearMap.congr_fun h v).symm
    simpa only [Module.End.mul_apply] using h2)

@[simp] theorem classFunctionIntertwiner_toLinearMap (f : ClassFunction G ℂ)
    (ρ : Representation ℂ G V) :
    (classFunctionIntertwiner f ρ).toLinearMap = classFunctionOperator f ρ := rfl

/-- **Schur's lemma (scalar form).** On a finite-dimensional irreducible complex
representation, the class-function operator `T_ρ f` is a scalar multiple of the identity. -/
theorem classFunctionOperator_eq_smul_id [FiniteDimensional ℂ V] (f : ClassFunction G ℂ)
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] :
    ∃ c : ℂ, classFunctionOperator f ρ = c • LinearMap.id := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective (classFunctionIntertwiner f ρ)
  refine ⟨c, ?_⟩
  have hL : classFunctionOperator f ρ
      = (algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c).toLinearMap := by
    rw [hc]; rfl
  rw [hL, Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul]
  congr 1

/-- The trace of `T_ρ f = ∑_g f(g) • ρ(g)` is `∑_g f(g) · χ_ρ(g)`. -/
theorem trace_classFunctionOperator [FiniteDimensional ℂ V] (f : ClassFunction G ℂ)
    (ρ : Representation ℂ G V) :
    LinearMap.trace ℂ V (classFunctionOperator f ρ) = ∑ g : G, f g * ρ.character g := by
  unfold classFunctionOperator
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- If `∑_g f(g) · χ_ρ(g) = 0` for a finite-dimensional irreducible representation `ρ`, then the
class-function operator `T_ρ f` vanishes: by Schur it is `c • id`, and the trace forces `c = 0`. -/
theorem classFunctionOperator_eq_zero_of_sum_eq_zero [FiniteDimensional ℂ V] [Nontrivial V]
    (f : ClassFunction G ℂ) (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (h : ∑ g : G, f g * ρ.character g = 0) :
    classFunctionOperator f ρ = 0 := by
  obtain ⟨c, hc⟩ := classFunctionOperator_eq_smul_id f ρ
  have hfr : 0 < finrank ℂ V := Module.finrank_pos
  have htr : c * (finrank ℂ V : ℂ) = 0 := by
    have e1 : LinearMap.trace ℂ V (classFunctionOperator f ρ) = c * (finrank ℂ V : ℂ) := by
      rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul]
    rw [trace_classFunctionOperator] at e1
    rw [← e1, h]
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp htr with hc0 | hfr0
    · exact hc0
    · exact absurd (Nat.cast_eq_zero.mp hfr0) hfr.ne'
  rw [hc, hc0, zero_smul]

end CFOp

section Transfer

variable {G : Type*} [Group G]

/-- Transport a representation `σ` on `W` along a linear equivalence `e : W ≃ₗ[ℂ] X`, giving a
representation on `X` (conjugation by `e`). Used to move a finite-dimensional representation to a
representative on `Fin n → ℂ`, a `Type 0` space. -/
noncomputable def transportRep {W X : Type*} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (e : W ≃ₗ[ℂ] X) :
    Representation ℂ G X :=
  ((e.conjRingEquiv : Module.End ℂ W ≃+* Module.End ℂ X).toRingHom.toMonoidHom).comp σ

@[simp] theorem transportRep_apply {W X : Type*} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (e : W ≃ₗ[ℂ] X) (g : G) :
    transportRep σ e g = e.conj (σ g) := rfl

/-- Transporting a representation preserves its character. -/
theorem transportRep_character {W X : Type*} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) (e : W ≃ₗ[ℂ] X) :
    (transportRep σ e).character = σ.character := by
  funext g
  change LinearMap.trace ℂ X (e.conj (σ g)) = LinearMap.trace ℂ W (σ g)
  exact LinearMap.trace_conj' (σ g) e

set_option backward.isDefEq.respectTransparency false in
/-- Transporting an irreducible representation along a linear equivalence keeps it irreducible. -/
theorem transportRep_isIrreducible {W X : Type*} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (e : W ≃ₗ[ℂ] X)
    [Representation.IsIrreducible σ] : Representation.IsIrreducible (transportRep σ e) := by
  -- rep equivalence `σ ≃ transportRep σ e` via `e`
  have he : ∀ g : G, (e : W →ₗ[ℂ] X) ∘ₗ σ g = (transportRep σ e) g ∘ₗ (e : W →ₗ[ℂ] X) := by
    intro g; ext w
    simp only [LinearMap.comp_apply, transportRep_apply, LinearEquiv.conj_apply_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  let φ : σ.Equiv (transportRep σ e) := Representation.Equiv.mk e he
  -- transport to `asModule` linear equivalence over `ℂ[G]`
  have hbij : Function.Bijective
      (Representation.IntertwiningMap.equivLinearMapAsModule σ (transportRep σ e)
        φ.toIntertwiningMap) :=
    e.bijective
  -- No type annotation on `L`: the `asModule` `MonoidAlgebra`-module instance is baked into the
  -- result of `equivLinearMapAsModule`, whereas re-stating the type would re-trigger (and fail)
  -- instance search on the `asModule` type synonym.
  let L := LinearEquiv.ofBijective
      (Representation.IntertwiningMap.equivLinearMapAsModule σ (transportRep σ e)
        φ.toIntertwiningMap) hbij
  have hσs := (Representation.irreducible_iff_isSimpleModule_asModule σ).mp
    ‹Representation.IsIrreducible σ›
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact IsSimpleModule.congr L.symm

/-- **Every finite-dimensional irreducible complex representation has its character among the
`IsIrreducibleCharacter`s.** (`IsIrreducibleCharacter` only quantifies over `Type 0` carriers;
this discharges the universe restriction by transporting to `Fin n → ℂ`.) -/
theorem exists_isIrreducibleCharacter_eq {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ G W) [Representation.IsIrreducible σ] :
    ∃ φ : ClassFunction G ℂ, IsIrreducibleCharacter φ ∧ (φ : G → ℂ) = σ.character := by
  let e : W ≃ₗ[ℂ] (Fin (finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun
  have : Representation.IsIrreducible (transportRep σ e) := transportRep_isIrreducible σ e
  refine ⟨repCharacterClassFunction (transportRep σ e),
    ⟨Fin (finrank ℂ W) → ℂ, inferInstance, inferInstance, inferInstance, transportRep σ e,
      inferInstance, rfl⟩, ?_⟩
  funext g
  exact congrFun (transportRep_character σ e) g

end Transfer

section EqualCharacter

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

set_option backward.isDefEq.respectTransparency false in
/-- **Irreducibility transports along an equivalence of representations.**  The underlying
linear equivalence upgrades to a `ℂ[G]`-linear equivalence of the `asModule`s
(`equivLinearMapAsModule`), and simplicity transports across it. -/
theorem Representation.IsIrreducible.of_equiv {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} [Representation.IsIrreducible ρ] (φ : ρ.Equiv σ) :
    Representation.IsIrreducible σ := by
  have hbij : Function.Bijective
      (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ φ.toIntertwiningMap) :=
    φ.toLinearEquiv.bijective
  let L := LinearEquiv.ofBijective
      (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ φ.toIntertwiningMap) hbij
  have := (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp
    ‹Representation.IsIrreducible ρ›
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact IsSimpleModule.congr L.symm

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- **A representation with the character of an irreducible one is isomorphic to it**
(character completeness for representations).  If `ρ` is irreducible and `σ` is any
finite-dimensional representation with `χ_σ = χ_ρ`, then `ρ ≅ σ` — `σ` is *not* assumed
irreducible.

`dim Hom_G(ρ, σ) = ⟨χ_σ, χ_ρ⟩ = ⟨χ_ρ, χ_ρ⟩ = dim Hom_G(ρ, ρ) = 1` (Schur), so there is a
nonzero intertwiner `T : ρ → σ`; its kernel is a proper subrepresentation of the irreducible
`ρ`, hence `⊥`, so `T` is injective; the dimensions agree (`χ_σ(1) = χ_ρ(1)`), so `T` is an
isomorphism. -/
theorem nonempty_equiv_of_character_eq [Finite G] [Invertible (Nat.card G : ℂ)]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (σ : Representation ℂ G W) (hchar : σ.character = ρ.character) :
    Nonempty (ρ.Equiv σ) := by
  have : Fintype G := Fintype.ofFinite _
  -- `dim Hom_G(ρ, σ) = dim Hom_G(ρ, ρ) = 1`
  have h1 := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  have h2 := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  rw [hchar] at h1
  have hrr : finrank ℂ (Representation.IntertwiningMap ρ ρ) = 1 := by
    have hbij : Function.Bijective
        (Algebra.linearMap ℂ (Representation.IntertwiningMap ρ ρ)) :=
      Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := ρ)
    rw [← (LinearEquiv.ofBijective _ hbij).finrank_eq, Module.finrank_self]
  have hfr : finrank ℂ (Representation.IntertwiningMap ρ σ) = 1 := by
    have h3 : ((finrank ℂ (Representation.IntertwiningMap ρ σ) : ℂ))
        = (finrank ℂ (Representation.IntertwiningMap ρ ρ) : ℂ) := h1.symm.trans h2
    have h4 : finrank ℂ (Representation.IntertwiningMap ρ σ)
        = finrank ℂ (Representation.IntertwiningMap ρ ρ) := by exact_mod_cast h3
    rw [h4, hrr]
  -- a nonzero intertwiner exists
  have : Nontrivial (Representation.IntertwiningMap ρ σ) :=
    Module.nontrivial_of_finrank_pos (by rw [hfr]; norm_num)
  obtain ⟨T, hT0⟩ := exists_ne (0 : Representation.IntertwiningMap ρ σ)
  -- its kernel is a proper subrepresentation of the irreducible `ρ`, hence trivial
  have hker : T.ker = ⊥ := by
    have h5 : IsSimpleOrder (Subrepresentation ρ) := ‹Representation.IsIrreducible ρ›
    rcases h5.eq_bot_or_eq_top T.ker with h | h
    · exact h
    · exfalso
      apply hT0
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      have hv : v ∈ T.ker := by
        have h6 : T.ker.toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule := by rw [h]
        have h7 : v ∈ T.ker.toSubmodule := by
          rw [h6]
          exact Submodule.mem_top
        exact h7
      rw [Representation.IntertwiningMap.mem_ker] at hv
      simpa using hv
  have hinj : Function.Injective T.toLinearMap := by
    rw [← LinearMap.ker_eq_bot]
    have h8 : T.ker.toSubmodule = LinearMap.ker T.toLinearMap := rfl
    rw [← h8, hker]
    rfl
  -- equal characters at `1` give equal dimensions, so `T` is an isomorphism
  have hdim : finrank ℂ V = finrank ℂ W := by
    have h9 : σ.character 1 = ρ.character 1 := congrFun hchar 1
    rw [Representation.char_one, Representation.char_one] at h9
    exact_mod_cast h9.symm
  have hsurj : Function.Surjective T.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨Representation.IntertwiningMap.ofBijective T ⟨hinj, hsurj⟩⟩

end EqualCharacter

section VirtualCharacters

variable {G : Type*} [Group G]

/-- `IsCompl` of subrepresentations descends to `IsCompl` of the underlying submodules
(`toSubmodule` is a bounded-lattice embedding). -/
theorem isCompl_toSubmodule {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {U U' : Subrepresentation ρ} (h : IsCompl U U') :
    IsCompl U.toSubmodule U'.toSubmodule := by
  constructor
  · rw [disjoint_iff, ← Subrepresentation.toSubmodule_inf, disjoint_iff.mp h.disjoint]
    rfl
  · rw [codisjoint_iff, ← Subrepresentation.toSubmodule_sup, codisjoint_iff.mp h.codisjoint]
    rfl

/-- **Trace additivity along a direct sum of subrepresentations.** If `U, U' : Subrepresentation ρ`
are complementary (`IsCompl U U'`), then `χ_ρ = χ_{U} + χ_{U'}` pointwise: the trace of `ρ g`
decomposes as the sum of the traces of its restrictions to `U` and `U'`.

The proof exhibits `ρ g` as the conjugate (by the iso `U.toSubmodule × U'.toSubmodule ≃ₗ V`) of the
product map of the two restrictions, then applies `LinearMap.trace_conj'` and
`LinearMap.trace_prodMap'`. -/
theorem character_add_of_isCompl {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (U U' : Subrepresentation ρ) (h : IsCompl U U') (g : G) :
    ρ.character g = U.toRepresentation.character g + U'.toRepresentation.character g := by
  -- `IsCompl` transports from `Subrepresentation ρ` to the underlying submodules.
  have hS : IsCompl U.toSubmodule U'.toSubmodule := isCompl_toSubmodule h
  set e : (U.toSubmodule × U'.toSubmodule) ≃ₗ[ℂ] V :=
    Submodule.prodEquivOfIsCompl U.toSubmodule U'.toSubmodule hS with he
  -- `ρ g` is the conjugate of the product of the two restrictions.
  have hconj : ρ g = e.conj
      (LinearMap.prodMap (U.toRepresentation g) (U'.toRepresentation g)) := by
    refine LinearMap.ext fun v => ?_
    rw [LinearEquiv.conj_apply_apply, LinearMap.prodMap_apply]
    -- `e (a, b) = ↑a + ↑b` for the prodEquivOfIsCompl.
    rw [he, Submodule.coe_prodEquivOfIsCompl']
    -- The two restrictions coerce back to `ρ g` applied to the coordinate (definitional);
    -- then `↑(e.symm v).1 + ↑(e.symm v).2 = e (e.symm v) = v`.
    have hsplit : ((e.symm v).1 : V) + ((e.symm v).2 : V) = v := by
      have := e.apply_symm_apply v
      rwa [he, Submodule.coe_prodEquivOfIsCompl'] at this
    change ρ g v = ρ g ((e.symm v).1 : V) + ρ g ((e.symm v).2 : V)
    rw [← map_add, hsplit]
  rw [show ρ.character g = LinearMap.trace ℂ V (ρ g) from rfl, hconj, LinearMap.trace_conj',
    LinearMap.trace_prodMap']
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **KEYSTONE.** The character of *any* finite-dimensional complex representation of a finite group
is a virtual character (`∈ ZIrr G`).

This is the universe-general, not-necessarily-irreducible extension of
`repCharacterClassFunction_mem_ZIrr`. The proof is strong induction on `finrank ℂ V`:
* `finrank = 0` ⇒ the character is `0 ∈ ZIrr G`.
* `ρ` irreducible ⇒ `exists_isIrreducibleCharacter_eq` exhibits `χ_ρ ∈ irreducibleCharacters G`,
  which lies in `ZIrr G`.
* `ρ` reducible (and nonzero) ⇒ by Maschke (`IsSemisimpleRepresentation`) a proper nonzero
  subrepresentation `U` has a complement `U'`; both have smaller `finrank`, and
  `character_add_of_isCompl` writes `χ_ρ = χ_U + χ_{U'}`, so the induction hypothesis and
  `Submodule.add_mem` conclude.

This is the keystone that unblocks `induce`/`restrict ∈ ZIrr` and hence the Dade isometry
(Peterfalvi (2.6.b)) / §9. -/
theorem character_mem_ZIrr {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {G : Type*} [Group G] [Finite G] (ρ : Representation ℂ G V) :
    (⟨ρ.character, fun g h => ρ.char_conj g h⟩ : ClassFunction G ℂ) ∈ ZIrr G := by
  classical
  -- Strong induction on `finrank ℂ V`, generalizing over the carrier `V'` (same universe).
  let motive : ℕ → Prop := fun n =>
    ∀ {V' : Type _} [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'],
      finrank ℂ V' = n → ∀ (ρ' : Representation ℂ G V'),
        (⟨ρ'.character, fun g h => ρ'.char_conj g h⟩ : ClassFunction G ℂ) ∈ ZIrr G
  refine (Nat.strongRecOn (motive := motive) (finrank ℂ V) ?_) rfl ρ
  clear ρ
  intro n ih V _ _ _ hn ρ
  -- Base case `finrank = 0`: the character is identically `0`.
  by_cases hn0 : n = 0
  · subst hn0
    have hV0 : finrank ℂ V = 0 := hn
    have : Subsingleton V := Module.finrank_zero_iff.mp hV0
    have hchar0 : (⟨ρ.character, fun g h => ρ.char_conj g h⟩ : ClassFunction G ℂ) = 0 := by
      apply ClassFunction.ext
      intro g
      change ρ.character g = 0
      rw [show ρ.character g = LinearMap.trace ℂ V (ρ g) from rfl,
        Subsingleton.elim (ρ g) 0, map_zero]
    rw [hchar0]
    exact Submodule.zero_mem _
  -- Otherwise `n > 0`, so `V` is nontrivial.
  have hpos : 0 < finrank ℂ V := by rw [hn]; exact Nat.pos_of_ne_zero hn0
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  by_cases hirr : Representation.IsIrreducible ρ
  · -- Irreducible case: the character is an irreducible character, hence in `ZIrr`.
    obtain ⟨φ, hφirr, hφeq⟩ := exists_isIrreducibleCharacter_eq ρ
    have : (⟨ρ.character, fun g h => ρ.char_conj g h⟩ : ClassFunction G ℂ) = φ := by
      apply ClassFunction.ext
      intro g
      rw [show ((⟨ρ.character, fun g h => ρ.char_conj g h⟩ : ClassFunction G ℂ) : G → ℂ) g
        = ρ.character g from rfl, congrFun hφeq g]
    rw [this]
    exact hφirr.mem_ZIrr
  · -- Reducible nonzero case: split off a proper nonzero subrepresentation.
    have : NeZero (Nat.card G : ℂ) :=
      ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
    -- `ρ` is not a simple order on `Subrepresentation ρ`; but it *is* nontrivial.
    have : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⟨⊥, ⊤, ?_⟩⟩
      intro hbt
      have : (⊥ : Subrepresentation ρ).toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule :=
        congrArg Subrepresentation.toSubmodule hbt
      simp only [show (⊥ : Subrepresentation ρ).toSubmodule = ⊥ from rfl,
        show (⊤ : Subrepresentation ρ).toSubmodule = ⊤ from rfl] at this
      exact absurd this.symm (top_ne_bot)
    -- From `¬ IsIrreducible` extract `U` with `U ≠ ⊥` and `U ≠ ⊤`.
    obtain ⟨U, hUbot, hUtop⟩ : ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by
      by_contra hcon
      push Not at hcon
      exact hirr ⟨fun U => or_iff_not_imp_left.mpr (hcon U)⟩
    -- Maschke gives a complement.
    obtain ⟨U', hUU'⟩ := ComplementedLattice.exists_isCompl U
    -- Both summands have strictly smaller finrank.
    have hUtop' : U.toSubmodule ≠ ⊤ := by
      intro h; exact hUtop (Subrepresentation.toSubmodule_injective
        (by rw [h]; rfl))
    have hUfin : finrank ℂ U.toSubmodule < finrank ℂ V := Submodule.finrank_lt hUtop'
    -- `U'.toSubmodule ≠ ⊤` because `U ≠ ⊥`.
    have hSc : IsCompl U.toSubmodule U'.toSubmodule := isCompl_toSubmodule hUU'
    have hU'top : U'.toSubmodule ≠ ⊤ := by
      intro htop
      apply hUbot
      apply Subrepresentation.toSubmodule_injective
      rw [show (⊥ : Subrepresentation ρ).toSubmodule = ⊥ from rfl]
      have : U.toSubmodule = U.toSubmodule ⊓ U'.toSubmodule := by rw [htop, inf_top_eq]
      rw [this, hSc.inf_eq_bot]
    have hU'fin : finrank ℂ U'.toSubmodule < finrank ℂ V := Submodule.finrank_lt hU'top
    -- Apply the induction hypothesis to both subrepresentations.
    have hIH_U := ih (finrank ℂ U.toSubmodule) (hn ▸ hUfin) rfl U.toRepresentation
    have hIH_U' := ih (finrank ℂ U'.toSubmodule) (hn ▸ hU'fin) rfl U'.toRepresentation
    -- The whole character is the sum of the two.
    have hsum : (⟨ρ.character, fun g h => ρ.char_conj g h⟩ : ClassFunction G ℂ)
        = (⟨U.toRepresentation.character, fun g h => U.toRepresentation.char_conj g h⟩ :
            ClassFunction G ℂ)
          + (⟨U'.toRepresentation.character, fun g h => U'.toRepresentation.char_conj g h⟩ :
            ClassFunction G ℂ) := by
      apply ClassFunction.ext
      intro g
      rw [ClassFunction.add_apply]
      exact character_add_of_isCompl ρ U U' hUU' g
    rw [hsum]
    exact Submodule.add_mem _ hIH_U hIH_U'

end VirtualCharacters

section Completeness

open scoped MonoidAlgebra

variable {G : Type*} [Group G]

/-- `f` precomposed with inversion, `g ↦ f g⁻¹`. A class function, since inversion permutes each
conjugacy class. -/
def classFunctionInv (f : ClassFunction G ℂ) : ClassFunction G ℂ :=
  ⟨fun g => f g⁻¹, fun g h => by
    change f (h * g * h⁻¹)⁻¹ = f g⁻¹
    rw [show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ from by group, f.conj_eq]⟩

@[simp] theorem classFunctionInv_apply (f : ClassFunction G ℂ) (g : G) :
    classFunctionInv f g = f g⁻¹ := rfl

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- If `f` is orthogonal to every irreducible character, then for every finite-dimensional
irreducible representation `σ`, `∑_g f(g⁻¹) · χ_σ(g) = 0`. (Reindexing by `g ↦ g⁻¹` and the
identity `χ_σ(g⁻¹) = conj χ_σ(g)` turn this sum into `|G| · (f, χ_σ)`, which vanishes since
`χ_σ ∈ Irr G`.) -/
theorem sum_classFunctionInv_character_eq_zero {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (f : ClassFunction G ℂ)
    (hf : ∀ χ : IrreducibleCharacter G, ClassFunction.inner f (χ : ClassFunction G ℂ) = 0)
    (σ : Representation ℂ G W) [Representation.IsIrreducible σ] :
    ∑ g : G, classFunctionInv f g * σ.character g = 0 := by
  obtain ⟨χ, hχirr, hχeq⟩ := exists_isIrreducibleCharacter_eq σ
  have hstep : ∑ g : G, classFunctionInv f g * σ.character g
      = ∑ g : G, f g * star ((χ : ClassFunction G ℂ) g) := by
    apply Fintype.sum_equiv (Equiv.inv G)
    intro g
    simp only [Equiv.inv_apply, classFunctionInv_apply]
    rw [congrFun hχeq g⁻¹, character_inv σ g, star_star]
  rw [hstep]
  have : ∑ g : G, f g * star ((χ : ClassFunction G ℂ) g)
      = ClassFunction.innerSum f (χ : ClassFunction G ℂ) := rfl
  rw [this, ← ClassFunction.card_mul_inner, hf ⟨χ, hχirr⟩, mul_zero]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
set_option backward.isDefEq.respectTransparency false in
/-- On the subrepresentation `ofSubmodule' N`, the `ℂ[G]`-action on `asModule` is the ambient action
restricted: `(c • v).val = c • v.val` (the right-hand smul taken in `ρ.asModule`). Reduces to
`Representation.single_smul` and `(ofSubmodule' N).toRepresentation g = (ρ g).restrict`. -/
theorem ofSubmodulePrime_coe_smul {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (N : Submodule ℂ[G] ρ.asModule) (c : ℂ[G])
    (v : (Subrepresentation.ofSubmodule' N).toRepresentation.asModule) :
    ((c • v).1 : ρ.asModule) = c • (show ρ.asModule from v.1) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_smul, add_smul, AddSubmonoid.coe_add, hx, hy]
  | single g a => rw [Representation.single_smul, Representation.single_smul]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- A `ℂ[G]`-submodule `N` of `ρ.asModule`, viewed as the subrepresentation `ofSubmodule' N`, has
its `asModule` `ℂ[G]`-linearly isomorphic to `N`. The underlying map is the identity on the shared
carrier (`↥N` and `↥(ofSubmodule' N).toSubmodule` are the same type definitionally); the only
content is `ℂ[G]`-linearity, supplied by `ofSubmodulePrime_coe_smul`. -/
noncomputable def ofSubmodulePrimeAsModuleEquiv {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (N : Submodule ℂ[G] ρ.asModule) :
    (↥N) ≃ₗ[ℂ[G]] (Subrepresentation.ofSubmodule' N).toRepresentation.asModule where
  toFun v := v
  invFun w := w
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c v := by
    apply Subtype.ext
    rw [RingHom.id_apply, Submodule.coe_smul]
    exact (ofSubmodulePrime_coe_smul ρ N c v).symm

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
set_option backward.isDefEq.respectTransparency false in
/-- For a simple `ℂ[G]`-submodule `N` of `ρ.asModule`, the subrepresentation `ofSubmodule' N` is
irreducible. -/
theorem ofSubmodulePrime_isIrreducible {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (N : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] (↥N)] :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' N).toRepresentation := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact (ofSubmodulePrimeAsModuleEquiv ρ N).isSimpleModule_iff.mp inferInstance

omit [Invertible (Nat.card G : ℂ)] in
set_option backward.isDefEq.respectTransparency false in
/-- The class-function operator on the subrepresentation `ofSubmodule' N` is the ambient operator
restricted: `(classFunctionOperator cf (ofSubmodule' N).toRepresentation w).val
= classFunctionOperator cf ρ w.val`. Each summand's value matches because
`(ofSubmodule' N).toRepresentation g = (ρ g).restrict`. -/
theorem classFunctionOperator_ofSubmodulePrime_coe (f : ClassFunction G ℂ) {W : Type*}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (N : Submodule ℂ[G] ρ.asModule)
    (w : (Subrepresentation.ofSubmodule' N).toRepresentation.asModule) :
    ((classFunctionOperator f (Subrepresentation.ofSubmodule' N).toRepresentation w).1 : W)
    = classFunctionOperator f ρ (show W from w.1) := by
  rw [classFunctionOperator, classFunctionOperator, LinearMap.sum_apply, LinearMap.sum_apply,
    AddSubmonoid.coe_finsetSum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Completeness of irreducible characters.** If `f : ClassFunction G ℂ` is orthogonal to every
irreducible character, then `f = 0`. Equivalently, the irreducible characters span the space of
class functions.

The proof uses the regular representation `reg = ofMulAction ℂ G G`. The class-function operator
`T = ∑_g f(g⁻¹) • reg g` is `ℂ[G]`-linear (an intertwiner). By Maschke's theorem `reg.asModule` is
a semisimple `ℂ[G]`-module, hence the supremum of its simple submodules is `⊤`. On each simple
submodule `N` the corresponding subrepresentation is irreducible (`ofSubmodulePrime_isIrreducible`),
so Schur's lemma forces `T` to vanish there (`classFunctionOperator_eq_zero_of_sum_eq_zero`, fed by
`sum_classFunctionInv_character_eq_zero`). Therefore `ker T = ⊤`, i.e. `T = 0`. Evaluating `T` at
`MonoidAlgebra.single 1 1` reads off `f(g⁻¹) = 0` for every `g`, so `f = 0`. -/
theorem classFunction_eq_zero_of_orthogonal (f : ClassFunction G ℂ)
    (hf : ∀ χ : IrreducibleCharacter G, ClassFunction.inner f (χ : ClassFunction G ℂ) = 0) :
    f = 0 := by
  have : Finite G := Finite.of_fintype G
  have : NeZero (Nat.card G : ℂ) := ⟨Invertible.ne_zero _⟩
  -- `Representation.ofMulAction` の対象は v4.32 で `G →₀ ℂ` から `ℂ[G]` (structure) になった。
  let reg : Representation ℂ G (MonoidAlgebra ℂ G) := Representation.ofMulAction ℂ G G
  have hreg : reg = Representation.ofMulAction ℂ G G := rfl
  -- The intertwiner `T = ∑_g f(g⁻¹) • reg g`, packaged as a `ℂ[G]`-linear `End` of `asModule`.
  set Ti : reg.asModule →ₗ[ℂ[G]] reg.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule reg reg
      (classFunctionIntertwiner (classFunctionInv f) reg) with hTi
  -- Register the canonical `AddCommGroup` instances on `G →₀ ℂ` and `reg.asModule` as
  -- zeta-transparent local instances: since the mathlib bump (module system), the nested
  -- unifications `Representation.instAddCommMonoidAsModule ≟ AddCommGroup.toAddCommMonoid ?_`
  -- (inside `Submodule.addCommGroup`) and the `Zero ℂ` argument of `Finsupp.instAddCommGroup`
  -- exceed the synthesis nesting limit when `V = G →₀ ℂ` is concrete, so `AddCommGroup ↥N`
  -- and `Representation.IsIrreducible σN` below would otherwise fail to elaborate.
  let : AddCommGroup (G →₀ ℂ) := inferInstance
  let : AddCommGroup reg.asModule := inferInstance
  -- Each simple `ℂ[G]`-submodule lies in `ker Ti`.
  have hsimple_le : ∀ N : Submodule ℂ[G] reg.asModule, IsSimpleModule ℂ[G] (↥N) →
      N ≤ LinearMap.ker Ti := by
    intro N hN
    have := hN
    have : Nontrivial (↥N) := IsSimpleModule.nontrivial ℂ[G] (↥N)
    set σN : Representation ℂ G _ := (Subrepresentation.ofSubmodule' N).toRepresentation with hσN
    have : Representation.IsIrreducible σN := ofSubmodulePrime_isIrreducible reg N
    have : Nontrivial ((Subrepresentation.ofSubmodule' N).toSubmodule) := ‹Nontrivial (↥N)›
    have : FiniteDimensional ℂ ((Subrepresentation.ofSubmodule' N).toSubmodule) :=
      inferInstance
    -- `T` restricted to the subrepresentation `σN` vanishes by Schur + orthogonality.
    have hzero : classFunctionOperator (classFunctionInv f) σN = 0 :=
      classFunctionOperator_eq_zero_of_sum_eq_zero (classFunctionInv f) σN
        (sum_classFunctionInv_character_eq_zero f hf σN)
    intro v hv
    -- `Ti v` equals the unbundled operator applied to `v`.
    have hTiv : Ti v = classFunctionOperator (classFunctionInv f) reg v := by
      rw [hTi]
      rfl
    -- The value of the restricted operator at `⟨v, _⟩` equals `Ti v`.
    have hmem : v ∈ (Subrepresentation.ofSubmodule' N).toSubmodule :=
      (Subrepresentation.mem_ofSubmodule'_iff).mpr hv
    rw [LinearMap.mem_ker, hTiv]
    have hval := classFunctionOperator_ofSubmodulePrime_coe (classFunctionInv f) reg N ⟨v, hmem⟩
    rw [hσN] at hzero
    rw [← hval, hzero]
    rfl
  -- `ker Ti = ⊤` since the supremum of simple submodules is `⊤` (Maschke).
  have : IsSemisimpleModule ℂ[G] reg.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule reg).mp inferInstance
  have hker : LinearMap.ker Ti = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← IsSemisimpleModule.sSup_simples_eq_top ℂ[G] reg.asModule]
    exact sSup_le fun N hN => hsimple_le N hN
  -- Hence `Ti = 0`, so the unbundled operator `T = ∑_g f(g⁻¹) • reg g` is `0`.
  have hTi0 : Ti = 0 := LinearMap.ker_eq_top.mp hker
  have hop0 : classFunctionOperator (classFunctionInv f) reg = 0 := by
    have : (Representation.IntertwiningMap.equivLinearMapAsModule reg reg).symm Ti
        = classFunctionIntertwiner (classFunctionInv f) reg := by
      rw [hTi, LinearEquiv.symm_apply_apply]
    rw [hTi0, map_zero] at this
    have h2 := congrArg Representation.IntertwiningMap.toLinearMap this.symm
    rwa [classFunctionIntertwiner_toLinearMap] at h2
  -- Evaluate `T` at `single 1 1` to read off `f (g⁻¹) = 0` for every `g`.
  apply ClassFunction.ext
  intro k
  classical
  have hcoeff : ∀ x : G, (classFunctionOperator (classFunctionInv f) reg
      (MonoidAlgebra.single (1 : G) (1 : ℂ))).coeff x = f x⁻¹ := by
    intro x
    rw [classFunctionOperator]
    have hterm : ∀ g : G,
        ((classFunctionInv f g • reg g) (MonoidAlgebra.single (1 : G) (1 : ℂ))).coeff x
          = if g = x then f g⁻¹ else 0 := by
      intro g
      rw [LinearMap.smul_apply, hreg, Representation.ofMulAction_single,
        MonoidAlgebra.smul_single, smul_eq_mul, mul_one, MonoidAlgebra.coeff_single,
        Finsupp.single_apply, smul_eq_mul, mul_one, classFunctionInv_apply, eq_comm]
    rw [LinearMap.sum_apply, MonoidAlgebra.coeff_finsetSum,
      Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_ite_eq' Finset.univ x]
    simp
  have := hcoeff k⁻¹
  rw [hop0] at this
  simpa using this.symm

end Completeness

section Count

variable {G : Type*} [Group G]

open Module (finrank)

/-- The linear functional "inner product against the irreducible characters", as a single
`ℂ`-linear map `ClassFunction G ℂ →ₗ[ℂ] (IrreducibleCharacter G → ℂ)`, `f ↦ (χ ↦ (f, χ))`.
`ClassFunction.inner` is `ℂ`-linear in its first argument, so this is well-defined; completeness
(`classFunction_eq_zero_of_orthogonal`) says it is injective. -/
noncomputable def innerAgainstIrreducibleCharacters [Fintype G] [Invertible (Nat.card G : ℂ)] :
    ClassFunction G ℂ →ₗ[ℂ] (IrreducibleCharacter G → ℂ) where
  toFun f χ := ClassFunction.inner f (χ : ClassFunction G ℂ)
  map_add' f₁ f₂ := by funext χ; exact ClassFunction.inner_add_left f₁ f₂ _
  map_smul' c f := by
    funext χ
    simpa using ClassFunction.inner_smul_left c f (χ : ClassFunction G ℂ)

/-- **`|Irr G| = |ConjClasses G|`** (Isaacs Thm 2.8 / Thm 6.10 count): the number of irreducible
complex characters of a finite group equals the number of conjugacy classes.

The `≤` direction is `card_irreducibleCharacter_le` (linear independence). For `≥`, completeness
(`classFunction_eq_zero_of_orthogonal`) makes the inner-product map
`innerAgainstIrreducibleCharacters : ClassFunction G ℂ →ₗ (IrreducibleCharacter G → ℂ)` injective,
whence `|ConjClasses G| = finrank ℂ (ClassFunction G ℂ) ≤ finrank ℂ (Irr G → ℂ) = |Irr G|`. -/
theorem card_irreducibleCharacter_eq [Finite G] :
    Nat.card (IrreducibleCharacter G) = Nat.card (ConjClasses G) := by
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have := finite_irreducibleCharacter (G := G)
  have : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  refine le_antisymm (card_irreducibleCharacter_le (G := G)) ?_
  -- The inner-product map against the irreducible characters is injective by completeness.
  have hinj : Function.Injective (innerAgainstIrreducibleCharacters (G := G)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    refine classFunction_eq_zero_of_orthogonal f fun χ => ?_
    exact congrFun hf χ
  -- Injectivity bounds the dimension of the class functions by `|Irr G|`.
  have hfr : finrank ℂ (ClassFunction G ℂ) ≤ finrank ℂ (IrreducibleCharacter G → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_classFunction (G := G), Module.finrank_fintype_fun_eq_card,
    ← Nat.card_eq_fintype_card (α := IrreducibleCharacter G)] at hfr
  exact hfr

/-- **The irreducible characters span the space of class functions.** Equivalently, every class
function is a `ℂ`-linear combination of irreducible characters (Isaacs Thm 2.8). Combines linear
independence (`linearIndependent_irreducibleCharacter`) with the count
`card_irreducibleCharacter_eq` and `finrank_classFunction`. -/
theorem span_irreducibleCharacter_eq_top [Finite G] :
    Submodule.span ℂ (Set.range (fun χ : IrreducibleCharacter G => (χ : ClassFunction G ℂ)))
      = ⊤ := by
  have := finite_irreducibleCharacter (G := G)
  have : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  have : Nonempty (IrreducibleCharacter G) := ⟨trivialIrreducibleCharacter G⟩
  refine LinearIndependent.span_eq_top_of_card_eq_finrank
    (linearIndependent_irreducibleCharacter (G := G)) ?_
  rw [finrank_classFunction (G := G), ← Nat.card_eq_fintype_card, card_irreducibleCharacter_eq]

/-- Fourier expansion of a class function in the irreducible-character basis.
The coefficient of `χ` is the normalized inner product `⟨f, χ⟩`. -/
theorem sum_inner_irreducibleCharacter_smul [Fintype G]
    [Fintype (IrreducibleCharacter G)] [Invertible (Nat.card G : ℂ)]
    (f : ClassFunction G ℂ) :
    (∑ χ : IrreducibleCharacter G,
        ClassFunction.inner f (χ : ClassFunction G ℂ) • (χ : ClassFunction G ℂ)) = f := by
  have horth : ∀ ψ : IrreducibleCharacter G,
      ClassFunction.inner
          (f - ∑ χ : IrreducibleCharacter G,
            ClassFunction.inner f (χ : ClassFunction G ℂ) • (χ : ClassFunction G ℂ))
          (ψ : ClassFunction G ℂ) = 0 := by
    intro ψ
    rw [ClassFunction.inner_sub_left]
    have hproj :
        ClassFunction.inner
            (∑ χ : IrreducibleCharacter G,
              ClassFunction.inner f (χ : ClassFunction G ℂ) • (χ : ClassFunction G ℂ))
            (ψ : ClassFunction G ℂ) =
          ClassFunction.inner f (ψ : ClassFunction G ℂ) := by
      change innerDual (ψ : ClassFunction G ℂ)
          (∑ χ : IrreducibleCharacter G,
            ClassFunction.inner f (χ : ClassFunction G ℂ) • (χ : ClassFunction G ℂ)) =
        ClassFunction.inner f (ψ : ClassFunction G ℂ)
      rw [map_sum]
      rw [Finset.sum_eq_single ψ]
      · rw [map_smul, innerDual_apply, irreducibleCharacter_inner, if_pos rfl, smul_eq_mul,
          mul_one]
      · intro χ _ hχψ
        rw [map_smul, innerDual_apply, irreducibleCharacter_inner, if_neg hχψ, smul_eq_mul,
          mul_zero]
      · intro hψ
        exact (hψ (Finset.mem_univ ψ)).elim
    rw [hproj, sub_self]
  have hzero := classFunction_eq_zero_of_orthogonal
    (f - ∑ χ : IrreducibleCharacter G,
      ClassFunction.inner f (χ : ClassFunction G ℂ) • (χ : ClassFunction G ℂ))
    fun ψ => horth ψ
  exact (sub_eq_zero.mp hzero).symm

end Count

section TableIndexing

open scoped Classical in
/-- **Hypothesis-free character-table indexing data** for a finite group, built from the count
`card_irreducibleCharacter_eq`. This discharges the cardinality input of
`CharacterTableIndexing.ofFinite`, so downstream column-orthogonality results (which take a
`CharacterTableIndexing G`) apply to any `[Finite G]`. -/
noncomputable def CharacterTableIndexing.ofFinite' (G : Type*) [Group G] [Finite G] :
    CharacterTableIndexing G := by
  haveI := finite_irreducibleCharacter (G := G)
  haveI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  refine CharacterTableIndexing.ofFinite (G := G) ?_
  let : Fintype (ConjClasses G) := conjClassesFintypeOfFinite G
  rw [← Nat.card_eq_fintype_card (α := IrreducibleCharacter G),
    ← Nat.card_eq_fintype_card (α := ConjClasses G), card_irreducibleCharacter_eq]

/-- A finite group canonically carries character-table indexing data. Not an `instance`
(`CharacterTableIndexing` is a structure, not a class); consumers bind it explicitly or
via `letI`. -/
noncomputable def instCharacterTableIndexingOfFinite {G : Type*} [Group G] [Finite G] :
    CharacterTableIndexing G :=
  CharacterTableIndexing.ofFinite' G

end TableIndexing

end OddOrder.RepresentationTheory


