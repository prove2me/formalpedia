-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_RepresentationDeterminant
-- name    : OddOrder_GroupTheory_RepresentationTheory_RepresentationDeterminant
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:05:28.644092+00:00
-- url     : https://prove2.me/theorems/34d4ff57-3e2d-47fe-b221-8fefd97488dc
-- title:
--   The determinant character of a representation
-- statement:
--   For a $\mathbb{C}$-representation $\rho$ of $G$, the map $g\mapsto\det(\rho(g))$ is a homomorphism $G\to\mathbb{C}^\times$, the determinant character $\det\rho$. It is well defined because each $\rho(g)$ is invertible and multiplicative because it is a composite of monoid homomorphisms.
--
--   Main definitions: `representationDeterminant` (the determinant character $\det\rho:G\to\mathbb{C}^\times$), `twistRep` (the twist of a representation by a linear character, $\beta(y)\rho(y)$) and `IsIrreducibleCharacter.determinant` (the determinantal character of an irreducible character).
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/RepresentationDeterminant.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/RepresentationDeterminant.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LinearCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RepresentationTheory.Basic

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The **determinant character** `det ρ : G →* ℂˣ` of a representation, `g ↦ det (ρ g)`.  A
homomorphism because it factors as `Units.map LinearMap.det ∘ ρ.asGroupHom` (`LinearMap.det` is a
monoid homomorphism `Module.End ℂ V →* ℂ`). -/
noncomputable def representationDeterminant (ρ : Representation ℂ G V) : G →* ℂˣ :=
  (Units.map (LinearMap.det : (V →ₗ[ℂ] V) →* ℂ)).comp ρ.asGroupHom

@[simp] theorem representationDeterminant_apply (ρ : Representation ℂ G V) (g : G) :
    (representationDeterminant ρ g : ℂ) = LinearMap.det (ρ g) := by
  rw [representationDeterminant, MonoidHom.comp_apply, Units.coe_map, ρ.asGroupHom_apply]

/-- The determinant character commutes with pullback along a homomorphism:
`det (ρ ∘ f) = (det ρ) ∘ f`.  With `f = H.subtype` this is `det (Res_H χ) = Res_H (det χ)` — the
determinantal character of an extension `χ ∈ Irr(I)` of `θ ∈ Irr(H)` restricts to `det θ`, the
compatibility that pins the coprime extension. -/
theorem representationDeterminant_comp {H : Type*} [Group H] (ρ : Representation ℂ G V)
    (f : H →* G) :
    representationDeterminant (ρ.comp f) = (representationDeterminant ρ).comp f := by
  ext h
  simp only [representationDeterminant_apply, MonoidHom.comp_apply]

/-- The **twist** of a representation by a linear character:
`(twistRep ρ β)(y) = β(y) • ρ(y)`.  It affords the product character `β · χ_ρ`
(`twistRep_character`), and its determinant is `β^{dim} · det ρ`
(`representationDeterminant_twistRep`) — the mechanism behind the determinantal
adjustment of extensions (Isaacs *CT* 6.25/6.28). -/
def twistRep (ρ : Representation ℂ G V) (β : G →* ℂˣ) : Representation ℂ G V where
  toFun y := (β y : ℂ) • ρ y
  map_one' := by simp
  map_mul' y₁ y₂ := by
    simp only [map_mul, Units.val_mul]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]

@[simp] theorem twistRep_apply (ρ : Representation ℂ G V) (β : G →* ℂˣ) (y : G) :
    twistRep ρ β y = (β y : ℂ) • ρ y :=
  rfl

/-- The twisted representation affords the product character `β · χ_ρ`. -/
theorem twistRep_character [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (β : G →* ℂˣ) (y : G) :
    (twistRep ρ β).character y = (β y : ℂ) * ρ.character y := by
  rw [Representation.character, twistRep_apply, map_smul]
  rfl

/-- The determinant of a twist: `det (β • ρ) = β^{dim V} · det ρ`. -/
theorem representationDeterminant_twistRep [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (β : G →* ℂˣ) (y : G) :
    representationDeterminant (twistRep ρ β) y
      = β y ^ Module.finrank ℂ V * representationDeterminant ρ y := by
  apply Units.ext
  rw [Units.val_mul, representationDeterminant_apply, representationDeterminant_apply,
    twistRep_apply, LinearMap.det_smul, Units.val_pow_eq_pow_val]

section CharacterDeterminant

/-- **The determinantal character of an irreducible character**: the determinant character
of a(ny) representation affording it.  `IsIrreducibleCharacter.determinant_spec` shows the
choice does not matter: any two affording representations are equivalent
(`nonempty_equiv_of_character_eq`), and the determinant is conjugation-invariant.

Its order `o(χ) = orderOf hχ.determinant` is the invariant steering the canonical coprime
extension (Isaacs *CT* 6.28/8.16, issue 9002 (v-c)). -/
noncomputable def IsIrreducibleCharacter.determinant {χ : ClassFunction G ℂ}
    (hχ : IsIrreducibleCharacter χ) : G →* ℂˣ :=
  letI := hχ.choose_spec.choose
  letI := hχ.choose_spec.choose_spec.choose
  representationDeterminant hχ.choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- **The determinantal character is representation-independent**: for any finite-dimensional
`σ` affording `χ`, `hχ.determinant = det σ`.  (`σ` is not assumed irreducible: it is
automatically equivalent to the chosen irreducible witness by
`nonempty_equiv_of_character_eq`, and `LinearMap.det` is invariant under conjugation by the
equivalence.) -/
theorem IsIrreducibleCharacter.determinant_spec [Finite G] {χ : ClassFunction G ℂ}
    (hχ : IsIrreducibleCharacter χ) {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ G W)
    (hσ : (χ : G → ℂ) = σ.character) :
    hχ.determinant = representationDeterminant σ := by
  let := hχ.choose_spec.choose
  let := hχ.choose_spec.choose_spec.choose
  let := hχ.choose_spec.choose_spec.choose_spec.choose
  obtain ⟨hirr₀, hchar₀⟩ := hχ.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have := hirr₀
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨Φ⟩ := nonempty_equiv_of_character_eq
    (hχ.choose_spec.choose_spec.choose_spec.choose_spec.choose) σ
    (by rw [← hσ, ← hchar₀])
  have hdet : ∀ y : G, LinearMap.det (σ y)
      = LinearMap.det (hχ.choose_spec.choose_spec.choose_spec.choose_spec.choose y) := by
    intro y
    rw [← Representation.Equiv.conj_apply_self y Φ,
      show Φ.conj (hχ.choose_spec.choose_spec.choose_spec.choose_spec.choose y)
          = (Φ.toLinearEquiv : _ →ₗ[ℂ] _)
            ∘ₗ ((hχ.choose_spec.choose_spec.choose_spec.choose_spec.choose y)
              ∘ₗ (Φ.toLinearEquiv.symm : _ →ₗ[ℂ] _)) from by
        rw [LinearEquiv.conj_apply, LinearMap.comp_assoc],
      LinearMap.det_conj]
  refine MonoidHom.ext fun y => Units.ext ?_
  have h0 : hχ.determinant = representationDeterminant
      (hχ.choose_spec.choose_spec.choose_spec.choose_spec.choose) := rfl
  rw [h0, representationDeterminant_apply, representationDeterminant_apply, hdet y]

/-- **Restriction compatibility**: the determinantal character of an irreducible restriction
is the restriction of the determinantal character.  (`hres` supplies the irreducibility of
the restricted character.) -/
theorem IsIrreducibleCharacter.determinant_restrict [Finite G] {H : Subgroup G}
    {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ)
    (hres : IsIrreducibleCharacter (ClassFunction.restrict H χ)) :
    hres.determinant = hχ.determinant.comp H.subtype := by
  obtain ⟨V', _, _, _, ρ, hρ, hc⟩ := id hχ
  have h2 : hres.determinant = representationDeterminant (ρ.comp H.subtype) := by
    refine IsIrreducibleCharacter.determinant_spec hres (ρ.comp H.subtype) ?_
    funext h
    rw [ClassFunction.restrict_apply]
    exact congrFun hc ((h : G))
  rw [h2, representationDeterminant_comp, IsIrreducibleCharacter.determinant_spec hχ ρ hc]

/-- **Pullback compatibility**: if the pullback `χ ∘ f` of an irreducible character along a
homomorphism `f : G' →* G` is again irreducible (e.g. for `f` surjective,
`IsIrreducibleCharacter.compHom_of_surjective`, or a group isomorphism), then its
determinantal character is the pullback `(det χ) ∘ f`.  Homomorphism-general form of
`IsIrreducibleCharacter.determinant_restrict`. -/
theorem IsIrreducibleCharacter.determinant_compHom [Finite G] {G' : Type*} [Group G']
    [Finite G'] {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ) (f : G' →* G)
    (hcomp : IsIrreducibleCharacter (ClassFunction.compHom f χ)) :
    hcomp.determinant = hχ.determinant.comp f := by
  obtain ⟨V', _, _, _, ρ, hρ, hc⟩ := id hχ
  have h1 : ((ClassFunction.compHom f χ : ClassFunction G' ℂ) : G' → ℂ)
      = Representation.character (ρ.comp f) := by
    funext y
    exact congrFun hc (f y)
  rw [IsIrreducibleCharacter.determinant_spec hcomp (ρ.comp f) h1,
    representationDeterminant_comp, IsIrreducibleCharacter.determinant_spec hχ ρ hc]

/-- **Precomposition with a surjective homomorphism preserves the order of a homomorphism
into a commutative monoid**: `orderOf (f ∘ e) = orderOf f` in the monoid of homomorphisms.
With `f = det χ` and `e` a group isomorphism (a conjugation, or a subgroup-of-subgroup
identification) this says the determinantal order `o(χ)` is invariant under transport —
the bookkeeping of the composition-series iterate (Isaacs *CT* 8.16, issue 9002 (v-d)). -/
theorem orderOf_monoidHom_comp_of_surjective {M M' N : Type*} [MulOneClass M] [MulOneClass M']
    [CommMonoid N] (f : M →* N) {e : M' →* M} (he : Function.Surjective e) :
    orderOf (f.comp e) = orderOf f := by
  refine Nat.dvd_antisymm ?_ ?_
  · refine orderOf_dvd_of_pow_eq_one (MonoidHom.ext fun y => ?_)
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply,
      pow_orderOf_eq_one, MonoidHom.one_apply, MonoidHom.one_apply]
  · refine orderOf_dvd_of_pow_eq_one (MonoidHom.ext fun x => ?_)
    obtain ⟨y, rfl⟩ := he x
    rw [MonoidHom.pow_apply, ← MonoidHom.comp_apply f e, ← MonoidHom.pow_apply,
      pow_orderOf_eq_one, MonoidHom.one_apply, MonoidHom.one_apply]

end CharacterDeterminant

end OddOrder.RepresentationTheory


