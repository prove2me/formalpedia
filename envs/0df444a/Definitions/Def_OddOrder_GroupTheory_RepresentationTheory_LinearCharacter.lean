-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LinearCharacter
-- name    : OddOrder_GroupTheory_RepresentationTheory_LinearCharacter
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:58:19.075459+00:00
-- url     : https://prove2.me/theorems/a06e2cc1-4ac1-4384-aab5-a3a17806e9f5
-- title:
--   Linear characters from group homomorphisms to $\mathbb{C}^\times$
-- statement:
--   A group homomorphism $\chi:H\to\mathbb{C}^\times$ defines a one-dimensional irreducible representation $h\mapsto\chi(h)\,\mathrm{id}$ of $H$ on $\mathbb{C}$, whose character is $h\mapsto\chi(h)$. This file packages these linear characters (degree-one irreducible characters) as `IrreducibleCharacter H` and records the API used by the Peterfalvi (6.8) construction of the family $Y=S(H')$, whose members are induced from the nontrivial linear characters of $H$ ($=\mathrm{Irr}(H/H')\setminus\{1\}$).
--
--   Main definitions: `linearClassFunction`, `linearIrreducibleCharacter`, and results that a degree-one irreducible character is multiplicative, has unit-modulus values, comes from a linear character, and that every irreducible character of a finite commutative group has degree one.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/LinearCharacter.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/LinearCharacter.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SchurCenterBound
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IrrIndexing
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

namespace OddOrder.RepresentationTheory

open scoped commutatorElement

variable {H : Type*} [Group H]

/-- The class function `h ↦ (χ h : ℂ)` attached to a homomorphism `χ : H →* ℂˣ`.  It is a
class function because the target `ℂˣ` is commutative. -/
def linearClassFunction (χ : H →* ℂˣ) : ClassFunction H ℂ :=
  ⟨fun h => (χ h : ℂ), fun g h =>
    congrArg (fun u : ℂˣ => (u : ℂ)) (by
      rw [map_mul, map_mul, map_inv, mul_comm (χ h) (χ g)]; group)⟩

@[simp] theorem linearClassFunction_apply (χ : H →* ℂˣ) (h : H) :
    (linearClassFunction χ) h = (χ h : ℂ) := rfl

/-- A homomorphism `χ : H →* ℂˣ` as a (linear, degree-one) irreducible character. -/
noncomputable def linearIrreducibleCharacter (χ : H →* ℂˣ) : IrreducibleCharacter H :=
  ⟨linearClassFunction χ, ℂ, inferInstance, inferInstance, inferInstance,
    { toFun := fun h => (χ h : ℂ) • (LinearMap.id : Module.End ℂ ℂ)
      map_one' := by
        rw [map_one, Units.val_one]; ext; simp [Module.End.one_apply]
      map_mul' := fun h₁ h₂ => by
        rw [map_mul, Units.val_mul]; ext
        simp [Module.End.mul_apply, smul_smul, mul_comm] },
    isIrreducible_complex_rep _, by
      funext h
      change (χ h : ℂ) = LinearMap.trace ℂ ℂ ((χ h : ℂ) • LinearMap.id)
      rw [map_smul, LinearMap.trace_id]; simp⟩

@[simp] theorem linearIrreducibleCharacter_coe (χ : H →* ℂˣ) :
    (linearIrreducibleCharacter χ : ClassFunction H ℂ) = linearClassFunction χ := rfl

@[simp] theorem linearIrreducibleCharacter_apply (χ : H →* ℂˣ) (h : H) :
    ((linearIrreducibleCharacter χ : ClassFunction H ℂ)) h = (χ h : ℂ) := rfl

@[simp] theorem linearIrreducibleCharacter_apply_one (χ : H →* ℂˣ) :
    ((linearIrreducibleCharacter χ : ClassFunction H ℂ)) (1 : H) = 1 := by
  rw [linearIrreducibleCharacter_apply, map_one, Units.val_one]

@[simp] theorem ClassFunction.compHom_linearIrreducibleCharacter
    {K H : Type*} [Group K] [Group H] (f : K →* H) (χ : H →* ℂˣ) :
    ClassFunction.compHom f
        (linearIrreducibleCharacter χ : ClassFunction H ℂ) =
      (linearIrreducibleCharacter (χ.comp f) : ClassFunction K ℂ) := by
  ext k
  rfl

theorem linearIrreducibleCharacter_injective :
    Function.Injective (linearIrreducibleCharacter (H := H)) := by
  intro χ₁ χ₂ h
  refine MonoidHom.ext fun g => Units.val_injective ?_
  have hg : ((linearIrreducibleCharacter χ₁ : ClassFunction H ℂ)) g =
      ((linearIrreducibleCharacter χ₂ : ClassFunction H ℂ)) g :=
    congrArg (fun c : ClassFunction H ℂ => c g) (Subtype.ext_iff.mp h)
  simpa only [linearIrreducibleCharacter_apply] using hg

@[simp] theorem linearIrreducibleCharacter_eq_trivial_iff {χ : H →* ℂˣ} :
    linearIrreducibleCharacter χ = trivialIrreducibleCharacter H ↔ χ = 1 := by
  rw [Subtype.ext_iff]
  constructor
  · intro h
    refine MonoidHom.ext fun g => ?_
    have hg : ((χ g : ℂ)) = 1 := by
      have := congrArg (fun c : ClassFunction H ℂ => c g) h
      simpa [linearClassFunction_apply, trivialClassFunction_apply] using this
    simpa using Units.val_eq_one.mp hg
  · intro h
    subst h
    ext g
    simp [linearClassFunction_apply, trivialClassFunction_apply]

variable {G : Type*} [Group G]

/-- On a 1-dimensional `ℂ`-representation, every operator `ρ g` is the scalar `ρ.character g`
times the identity. -/
theorem finrank_one_rep_apply_eq_character_smul_id {V : Type*} [AddCommGroup V]
    [Module ℂ V] [Module.Finite ℂ V] (ρ : Representation ℂ G V) (hdim : Module.finrank ℂ V = 1)
    (g : G) :
    ρ g = (ρ.character g) • (LinearMap.id : Module.End ℂ V) := by
  obtain ⟨v, _hv_ne, hv⟩ := finrank_eq_one_iff'.mp hdim
  -- `ρ g` is some scalar `c` on the spanning vector `v`; that scalar is the trace.
  obtain ⟨c, hc⟩ := hv (ρ g v)
  have hsmul : ρ g = c • (LinearMap.id : Module.End ℂ V) := by
    apply LinearMap.ext
    intro w
    obtain ⟨d, rfl⟩ := hv w
    rw [map_smul, ← hc, LinearMap.smul_apply, LinearMap.id_apply, smul_comm]
  have htrace : ρ.character g = c := by
    rw [Representation.character, hsmul, map_smul, LinearMap.trace_id, hdim]; simp
  rw [hsmul, htrace]

variable [Finite G]

omit [Finite G] in
/-- A degree-one irreducible character is **multiplicative**: `θ(g·h) = θ(g)·θ(h)`.

The witnessing representation is 1-dimensional (its degree is `θ(1) = 1`), so every operator is a
scalar (`finrank_one_rep_apply_eq_character_smul_id`) and the trace map `θ = χ_ρ` is multiplicative
on scalars. -/
theorem IsIrreducibleCharacter.map_mul_of_apply_one_eq_one {φ : ClassFunction G ℂ}
    (hφ : IsIrreducibleCharacter φ) (h1 : (φ : G → ℂ) 1 = 1) (g h : G) :
    (φ : G → ℂ) (g * h) = (φ : G → ℂ) g * (φ : G → ℂ) h := by
  obtain ⟨V, _, _, _, ρ, _, hχ⟩ := hφ
  have hdim : Module.finrank ℂ V = 1 := by
    have hc : (Module.finrank ℂ V : ℂ) = 1 := by
      rw [← ρ.char_one, ← congrFun hχ 1]; exact h1
    exact_mod_cast hc
  have hg := finrank_one_rep_apply_eq_character_smul_id ρ hdim g
  have hh := finrank_one_rep_apply_eq_character_smul_id ρ hdim h
  have hgh := finrank_one_rep_apply_eq_character_smul_id ρ hdim (g * h)
  -- `char(gh) • id = (char g • id)*(char h • id) = (char g · char h) • id`; take traces.
  rw [map_mul, hg, hh, smul_mul_smul_comm, Module.End.mul_eq_comp, LinearMap.id_comp] at hgh
  have hval := congrArg (fun f : Module.End ℂ V => LinearMap.trace ℂ V f) hgh
  simp only [map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, mul_one] at hval
  rw [congrFun hχ (g * h), congrFun hχ g, congrFun hχ h]
  exact hval.symm

omit [Finite G] in
/-- A degree-one irreducible character has unit-modulus values, in particular `θ(g) ≠ 0`.

From multiplicativity, `θ(g)·θ(g⁻¹) = θ(1) = 1`. -/
theorem IsIrreducibleCharacter.apply_ne_zero_of_apply_one_eq_one {φ : ClassFunction G ℂ}
    (hφ : IsIrreducibleCharacter φ) (h1 : (φ : G → ℂ) 1 = 1) (g : G) :
    (φ : G → ℂ) g ≠ 0 := by
  intro h0
  have hmul := hφ.map_mul_of_apply_one_eq_one h1 g g⁻¹
  rw [mul_inv_cancel, h1, h0, zero_mul] at hmul
  exact one_ne_zero hmul

omit [Finite G] in
/-- A degree-one irreducible character is induced by a multiplicative linear character
`G →* ℂˣ`.

This is the converse packaging to `linearIrreducibleCharacter`: multiplicativity of `φ` gives a
homomorphism into `ℂ`, and `apply_ne_zero_of_apply_one_eq_one` upgrades the values to units. -/
theorem IsIrreducibleCharacter.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one
    {φ : ClassFunction G ℂ} (hφ : IsIrreducibleCharacter φ) (h1 : (φ : G → ℂ) 1 = 1) :
    ∃ χ : G →* ℂˣ, (linearIrreducibleCharacter χ : ClassFunction G ℂ) = φ := by
  let χ : G →* ℂˣ :=
    { toFun := fun g => Units.mk0 ((φ : G → ℂ) g)
        (hφ.apply_ne_zero_of_apply_one_eq_one h1 g)
      map_one' := by
        ext
        exact h1
      map_mul' := fun g h => by
        ext
        exact hφ.map_mul_of_apply_one_eq_one h1 g h }
  refine ⟨χ, ?_⟩
  ext g
  simp [χ]

omit [Finite G] in
/-- Every irreducible character of a finite commutative group is degree one. -/
theorem IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative [IsMulCommutative G]
    {φ : ClassFunction G ℂ} (hφ : IsIrreducibleCharacter φ) :
    (φ : G → ℂ) 1 = 1 := by
  obtain ⟨V, _, _, _, ρ, hirr, hχ⟩ := hφ
  have : Representation.IsIrreducible ρ := hirr
  have := nontrivial_of_isIrreducible ρ
  have hdim : Module.finrank ℂ V = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρ)
  rw [congrFun hχ 1, ρ.char_one, hdim, Nat.cast_one]

omit [Finite G] in
/-- Every irreducible character of a finite commutative group comes from a linear character. -/
theorem IsIrreducibleCharacter.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
    [IsMulCommutative G] {φ : ClassFunction G ℂ} (hφ : IsIrreducibleCharacter φ) :
    ∃ χ : G →* ℂˣ, (linearIrreducibleCharacter χ : ClassFunction G ℂ) = φ :=
  hφ.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one
    hφ.apply_one_eq_one_of_isMulCommutative

omit [Finite G] in
/-- A degree-one irreducible character **kills commutators**: `θ(⁅a,b⁆) = θ(1) = 1`.

`θ` is a homomorphism into the commutative monoid `(ℂ, ·)` on the (nonvanishing) values, so the
image of a commutator is `1`. -/
theorem IsIrreducibleCharacter.apply_commutatorElement_eq_one_of_apply_one_eq_one
    {φ : ClassFunction G ℂ} (hφ : IsIrreducibleCharacter φ) (h1 : (φ : G → ℂ) 1 = 1) (a b : G) :
    (φ : G → ℂ) ⁅a, b⁆ = 1 := by
  have hmul := hφ.map_mul_of_apply_one_eq_one h1
  have ha := hφ.apply_ne_zero_of_apply_one_eq_one h1 a
  have hb := hφ.apply_ne_zero_of_apply_one_eq_one h1 b
  -- `θ(a⁻¹) = θ(a)⁻¹` and likewise for `b`, since `θ(a)·θ(a⁻¹) = θ(1) = 1`.
  have hainv : (φ : G → ℂ) a * (φ : G → ℂ) a⁻¹ = 1 := by
    rw [← hmul a a⁻¹, mul_inv_cancel, h1]
  have hbinv : (φ : G → ℂ) b * (φ : G → ℂ) b⁻¹ = 1 := by
    rw [← hmul b b⁻¹, mul_inv_cancel, h1]
  rw [commutatorElement_def, hmul, hmul, hmul]
  -- `θ(a)·θ(b)·θ(a⁻¹)·θ(b⁻¹) = (θa·θa⁻¹)·(θb·θb⁻¹) = 1`.
  calc
    (φ : G → ℂ) a * (φ : G → ℂ) b * (φ : G → ℂ) a⁻¹ * (φ : G → ℂ) b⁻¹
        = ((φ : G → ℂ) a * (φ : G → ℂ) a⁻¹) * ((φ : G → ℂ) b * (φ : G → ℂ) b⁻¹) := by ring
    _ = 1 := by rw [hainv, hbinv, mul_one]

omit [Finite G] in
/-- A degree-one irreducible character is **trivial on the commutator subgroup**: `θ(n) = 1` for
every `n ∈ commutator G`.

The commutator-element values `θ(⁅a,b⁆) = 1`
(`apply_commutatorElement_eq_one_of_apply_one_eq_one`) extend to the whole derived subgroup because
`θ` is induced by a homomorphism `χ : G →* ℂˣ`
(`exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one`) into the *commutative* group `ℂˣ`,
whose kernel therefore contains `⁅⊤, ⊤⁆ = commutator G`. -/
theorem IsIrreducibleCharacter.apply_eq_one_of_mem_commutator_of_apply_one_eq_one
    {φ : ClassFunction G ℂ} (hφ : IsIrreducibleCharacter φ) (h1 : (φ : G → ℂ) 1 = 1)
    {n : G} (hn : n ∈ commutator G) : (φ : G → ℂ) n = 1 := by
  obtain ⟨χ, hχ⟩ := hφ.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one h1
  have hker : commutator G ≤ χ.ker := by
    rw [commutator_def]
    exact Subgroup.commutator_le.mpr fun a _ b _ => by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact Commute.all (χ a) (χ b)
  have hn1 : χ n = 1 := MonoidHom.mem_ker.mp (hker hn)
  rw [← hχ]
  simp only [linearIrreducibleCharacter_apply, hn1, Units.val_one]

end OddOrder.RepresentationTheory


