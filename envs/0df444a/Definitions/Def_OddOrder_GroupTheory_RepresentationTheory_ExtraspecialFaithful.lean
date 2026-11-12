-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtraspecialFaithful
-- name    : OddOrder_GroupTheory_RepresentationTheory_ExtraspecialFaithful
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:49:46.068504+00:00
-- url     : https://prove2.me/theorems/b8f4ddc2-c37b-4c4c-8664-c414d01e8b9d
-- title:
--   Faithful representations of extraspecial $p$-groups (BG §2 Thm 2.5 / Gorenstein 5.5.5)
-- statement:
--   Towards Gorenstein 5.5.5: a faithful irreducible representation of an extraspecial $q$-group $P$ of order $q^{1+2n}$ over an algebraically closed field of characteristic not dividing $|P|$ has dimension $q^n$. The proof uses the character mass formula.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ExtraspecialFaithful.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ExtraspecialFaithful.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_AbsolutelyIrreducible
import Definitions.Def_OddOrder_GroupTheory_IsExtraspecial
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Commutator.Basic

namespace OddOrder.RepresentationTheory

open Representation

open scoped commutatorElement

variable {F : Type*} [Field F] [IsAlgClosed F]

variable {P : Type*} [Group P] {V : Type*} [AddCommGroup V] [Module F V]

/-- **The character of a faithful irreducible vanishes off the center** (Gor 5.5.5, geometric step).

If `ρ` is a faithful irreducible representation over an algebraically closed field `F`, `P` has
nilpotency class `≤ 2` (`commutator P ≤ Z(P)`), and `g ∉ Z(P)`, then `χ(g) = 0`.

For `g ∉ Z(P)` there is `x` with `z₀ := ⁅x, g⁆ ≠ 1`; as `[P,P] ⊆ Z(P)`, `z₀` is central and
`x g x⁻¹ = z₀ g`, so `χ(g) = χ(z₀ g) = c · χ(g)` where `ρ z₀ = c • id` and `c ≠ 1` (faithfulness),
forcing `χ(g) = 0`. -/
theorem character_eq_zero_of_notMem_center [FiniteDimensional F V]
    (ρ : Representation F P V) [ρ.IsIrreducible] (hf : Function.Injective ρ)
    (hcl : commutator P ≤ Subgroup.center P) {g : P} (hg : g ∉ Subgroup.center P) :
    ρ.character g = 0 := by
  -- a non-commuting partner of `g`
  obtain ⟨x, hx⟩ : ∃ x : P, x * g ≠ g * x := by
    by_contra h
    exact hg (Subgroup.mem_center_iff.mpr fun y => not_not.mp fun hy => h ⟨y, hy⟩)
  -- `z₀ := ⁅x, g⁆` is a nontrivial central element
  have hz₀ne : ⁅x, g⁆ ≠ 1 := by rw [Ne, commutatorElement_eq_one_iff_mul_comm]; exact hx
  have hz₀mem : ⁅x, g⁆ ∈ Subgroup.center P := by
    apply hcl
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top g)
  -- it acts as a scalar `c`, with `c ≠ 1` by faithfulness
  obtain ⟨c, hc⟩ := center_isScalar ρ hz₀mem
  have hcne : c ≠ 1 := by
    intro hc1
    apply hz₀ne
    apply hf
    rw [map_one, hc, hc1, one_smul, Module.End.one_eq_id]
  -- `x g x⁻¹ = ⁅x, g⁆ * g`
  have hconj : x * g * x⁻¹ = ⁅x, g⁆ * g := by rw [commutatorElement_def]; group
  -- `χ(g) = χ(x g x⁻¹) = χ(z₀ g) = c · χ(g)`
  have key : ρ.character g = c * ρ.character g :=
    calc ρ.character g = ρ.character (x * g * x⁻¹) := (Representation.char_conj ρ g x).symm
      _ = ρ.character (⁅x, g⁆ * g) := by rw [hconj]
      _ = c * ρ.character g := by
          rw [Representation.character, Representation.character, map_mul, hc,
            ← Module.End.one_eq_id, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  -- conclude `χ(g) = 0`
  have h1c : (1 : F) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hcne)
  have hzero : (1 - c) * ρ.character g = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left h1c

/-- **On the center, `χ(g) · χ(g⁻¹) = (dim V)²`** (Gor 5.5.5 step). A central element acts as a
scalar `c` (with `g⁻¹` acting as `c'` and `c·c'·(dim V) = dim V` from `ρ g · ρ g⁻¹ = 1`), so
`χ(g) = c·(dim V)`, `χ(g⁻¹) = c'·(dim V)`, and the product collapses to `(dim V)²`. -/
theorem char_mul_char_inv_of_mem_center [FiniteDimensional F V]
    (ρ : Representation F P V) [ρ.IsIrreducible] {g : P} (hg : g ∈ Subgroup.center P) :
    ρ.character g * ρ.character g⁻¹ = (Module.finrank F V : F) ^ 2 := by
  obtain ⟨c, hc⟩ := center_isScalar ρ hg
  obtain ⟨c', hc'⟩ := center_isScalar ρ (Subgroup.inv_mem _ hg)
  rw [← Module.End.one_eq_id] at hc hc'
  have hchar : ρ.character g = c * (Module.finrank F V : F) := by
    change LinearMap.trace F V (ρ g) = _
    rw [hc, map_smul, LinearMap.trace_one, smul_eq_mul]
  have hchar' : ρ.character g⁻¹ = c' * (Module.finrank F V : F) := by
    change LinearMap.trace F V (ρ g⁻¹) = _
    rw [hc', map_smul, LinearMap.trace_one, smul_eq_mul]
  -- `(c·c') • 1 = ρ g · ρ g⁻¹ = ρ 1 = 1`, hence `c·c'·(dim V) = dim V`.
  have hone : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hprod : (c * c') • (1 : Module.End F V) = 1 := by
    have hmul : (c • (1 : Module.End F V)) * (c' • 1) = (c * c') • 1 := by
      rw [smul_mul_smul_comm, one_mul]
    rw [← hmul, ← hc, ← hc']; exact hone
  have hcc : c * c' * (Module.finrank F V : F) = (Module.finrank F V : F) := by
    have h := congrArg (LinearMap.trace F V) hprod
    rwa [map_smul, LinearMap.trace_one, smul_eq_mul] at h
  rw [hchar, hchar']
  have hrearrange : c * (Module.finrank F V : F) * (c' * (Module.finrank F V : F))
      = c * c' * (Module.finrank F V : F) * (Module.finrank F V : F) := by ring
  rw [hrearrange, hcc, ← pow_two]

/-- **Character mass formula** (Gor 5.5.5a-ii): for a faithful irreducible representation `ρ` of a
finite group `P` of nilpotency class `≤ 2` (`commutator P ≤ Z(P)`) over an algebraically closed
field with `char ∤ |P|`, `(dim V)² · |Z(P)| = |P|` (an equation in `F`).

By `char_orthonormal` the sum `∑_g χ(g)χ(g⁻¹)` is `|P|`; the character vanishes off `Z(P)`
(`character_eq_zero_of_notMem_center`) and equals `(dim V)²` on each central element
(`char_mul_char_inv_of_mem_center`), so the sum is `|Z(P)| · (dim V)²`. -/
theorem sq_finrank_mul_card_center [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P) :
    (Module.finrank F V : F) ^ 2 * (Nat.card (Subgroup.center P) : F) = (Nat.card P : F) := by
  classical
  have : Fintype P := Fintype.ofFinite P
  have hne : (Nat.card P : F) ≠ 0 := (isUnit_of_invertible _).ne_zero
  -- orthonormality `⟹ ∑ χ(g) χ(g⁻¹) = |P|`
  have hortho := Representation.char_orthonormal ρ ρ
  rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at hortho
  have hsum : ∑ g : P, ρ.character g * ρ.character g⁻¹ = (Nat.card P : F) := by
    have h := congrArg (fun x => (Nat.card P : F) * x) hortho
    simp only [← mul_assoc, mul_inv_cancel₀ hne, one_mul, mul_one] at h
    exact h
  -- each term is `(dim V)²` on the center and `0` off it
  have hterm : ∀ g : P, ρ.character g * ρ.character g⁻¹
      = if g ∈ Subgroup.center P then (Module.finrank F V : F) ^ 2 else 0 := by
    intro g
    by_cases hg : g ∈ Subgroup.center P
    · rw [if_pos hg, char_mul_char_inv_of_mem_center ρ hg]
    · rw [if_neg hg, character_eq_zero_of_notMem_center ρ hf hcl hg, zero_mul]
  -- count: `|{g : g ∈ Z}| = |Z|`
  have hcard : (Finset.univ.filter (· ∈ Subgroup.center P)).card
      = Nat.card (Subgroup.center P) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- assemble the split sum
  have hsplit : ∑ g : P, ρ.character g * ρ.character g⁻¹
      = (Nat.card (Subgroup.center P) : F) * (Module.finrank F V : F) ^ 2 :=
    calc ∑ g : P, ρ.character g * ρ.character g⁻¹
        = ∑ g : P, if g ∈ Subgroup.center P then (Module.finrank F V : F) ^ 2 else 0 :=
          Finset.sum_congr rfl (fun g _ => hterm g)
      _ = ∑ _g ∈ Finset.univ.filter (· ∈ Subgroup.center P), (Module.finrank F V : F) ^ 2 :=
          (Finset.sum_filter _ _).symm
      _ = (Finset.univ.filter (· ∈ Subgroup.center P)).card • (Module.finrank F V : F) ^ 2 :=
          Finset.sum_const _
      _ = (Nat.card (Subgroup.center P) : F) * (Module.finrank F V : F) ^ 2 := by
          rw [nsmul_eq_mul, hcard]
  rw [mul_comm, ← hsplit]
  exact hsum

/-- **`(dim V : F) ≠ 0`** (Gor 5.5.5a-iii). Bootstrapped from the mass formula: if `(dim V : F) = 0`
then `(dim V)² · |Z| = 0 ≠ |P|`, contradicting `char ∤ |P|`. This is what makes the trace-form Gram
matrix nonsingular in the integer step. -/
theorem finrank_cast_ne_zero [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P) :
    (Module.finrank F V : F) ≠ 0 := by
  intro h
  apply (isUnit_of_invertible (Nat.card P : F)).ne_zero
  have hmass := sq_finrank_mul_card_center ρ hf hcl
  rw [h] at hmass
  rw [← hmass]; ring

/-- **`|P/Z| ≤ (dim V)²`** (Gor 5.5.5a-v, the trace-form independence half). The `|P/Z|` images
`ρ(out c)` of `Z`-coset representatives are `F`-linearly independent in `End_F V`: pairing with the
functional `A ↦ trace(A · ρ(out c')⁻¹)` gives the Gram matrix `χ(out c · (out c')⁻¹) = δ · (dim V)`,
nonsingular because `(dim V : F) ≠ 0`. Hence `card (P ⧸ Z) ≤ finrank (End_F V) = (dim V)²`. -/
theorem card_quotient_center_le_sq_finrank [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P) :
    Nat.card (P ⧸ Subgroup.center P) ≤ Module.finrank F V ^ 2 := by
  classical
  have : Fintype P := Fintype.ofFinite P
  have : Fintype (P ⧸ Subgroup.center P) := Fintype.ofFinite _
  -- coset membership of `out c · (out c')⁻¹` ↔ `c = c'`
  have hco : ∀ c : P ⧸ Subgroup.center P, (↑(Quotient.out c) : P ⧸ Subgroup.center P) = c :=
    fun c => Quotient.out_eq' c
  have hmem : ∀ c c' : P ⧸ Subgroup.center P,
      Quotient.out c * (Quotient.out c')⁻¹ ∈ Subgroup.center P ↔ c = c' := by
    intro c c'
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hco, hco]
    exact mul_inv_eq_one
  -- trace-form Gram entries
  have hTval : ∀ c c' : P ⧸ Subgroup.center P,
      LinearMap.trace F V (ρ (Quotient.out c) * ρ ((Quotient.out c')⁻¹))
        = if c = c' then (Module.finrank F V : F) else 0 := by
    intro c c'
    rw [← map_mul]
    change ρ.character _ = _
    by_cases h : c = c'
    · subst h; rw [if_pos rfl, mul_inv_cancel, char_one]
    · rw [if_neg h]
      exact character_eq_zero_of_notMem_center ρ hf hcl ((hmem c c').not.mpr h)
  -- the family of coset-rep images is linearly independent
  have hindep : LinearIndependent F (fun c : P ⧸ Subgroup.center P => ρ (Quotient.out c)) := by
    rw [Fintype.linearIndependent_iff]
    intro coef hcoef j
    have happ : LinearMap.trace F V
          ((∑ i, coef i • ρ (Quotient.out i)) * ρ ((Quotient.out j)⁻¹))
        = ∑ i, coef i • LinearMap.trace F V (ρ (Quotient.out i) * ρ ((Quotient.out j)⁻¹)) := by
      rw [Finset.sum_mul, map_sum]
      simp only [smul_mul_assoc, map_smul]
    rw [hcoef, zero_mul, map_zero] at happ
    simp only [hTval, smul_ite, smul_zero] at happ
    rw [Finset.sum_ite_eq' Finset.univ j] at happ
    simp only [Finset.mem_univ, if_true, smul_eq_mul] at happ
    exact (mul_eq_zero.mp happ.symm).resolve_right (finrank_cast_ne_zero ρ hf hcl)
  -- independence ⟹ card ≤ finrank End = (dim V)²
  have h1 := hindep.fintype_card_le_finrank
  rwa [Module.finrank_linearMap, ← pow_two, ← Nat.card_eq_fintype_card] at h1

/-- **Gorenstein 5.5.5a (integer form): `(dim V)² = |P/Z|`.** For a faithful irreducible
representation of a finite group `P` of nilpotency class `≤ 2` over an algebraically closed field
with `char ∤ |P|`, `(dim V)² = Nat.card (P ⧸ Z(P))`.

The `≥` direction is `card_quotient_center_le_sq_finrank` (trace-form independence). The `≤`
direction is spanning: by Burnside `End_F V` is spanned by `{ρ g}`, and each `ρ g` is a multiple of
`ρ(out ⟦g⟧)`, so the `|P/Z|` coset-rep images span `End_F V`, giving
`(dim V)² = finrank (End_F V) ≤ |P/Z|`. (This is the basis of BG (2.11).) -/
theorem sq_finrank_eq_card_quotient_center [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P) :
    Module.finrank F V ^ 2 = Nat.card (P ⧸ Subgroup.center P) := by
  classical
  have : Fintype P := Fintype.ofFinite P
  have : Fintype (P ⧸ Subgroup.center P) := Fintype.ofFinite _
  set v : (P ⧸ Subgroup.center P) → Module.End F V := fun c => ρ (Quotient.out c) with hv
  have hco : ∀ c : P ⧸ Subgroup.center P, (↑(Quotient.out c) : P ⧸ Subgroup.center P) = c :=
    fun c => Quotient.out_eq' c
  -- each `ρ g` is a scalar multiple of `v ⟦g⟧`, hence in `span (range v)`
  have hmem_span : ∀ g : P, ρ g ∈ Submodule.span F (Set.range v) := by
    intro g
    have hz : g * (Quotient.out (↑g : P ⧸ Subgroup.center P))⁻¹ ∈ Subgroup.center P := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hco]
      exact mul_inv_cancel _
    obtain ⟨s, hs⟩ := center_isScalar ρ hz
    have hgeq : g = g * (Quotient.out (↑g : P ⧸ Subgroup.center P))⁻¹
        * Quotient.out (↑g : P ⧸ Subgroup.center P) := by group
    rw [hgeq, map_mul, hs, ← Module.End.one_eq_id, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ s (Submodule.subset_span (Set.mem_range_self _))
  -- the family spans `End_F V` (Burnside)
  have hsub : ∀ r : MonoidAlgebra F P, ρ.asAlgebraHom r ∈ Submodule.span F (Set.range v) := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of g => rw [asAlgebraHom_of]; exact hmem_span g
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hspan : Submodule.span F (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro A _
    obtain ⟨r, rfl⟩ := asAlgebraHom_surjective_of_isAlgClosed ρ A
    exact hsub r
  -- spanning ⟹ `(dim V)² ≤ |P/Z|`
  have hle : Module.finrank F V ^ 2 ≤ Nat.card (P ⧸ Subgroup.center P) := by
    have hfr : Module.finrank F (Module.End F V) ≤ Nat.card (P ⧸ Subgroup.center P) :=
      calc Module.finrank F (Module.End F V)
          = Module.finrank F ↥(Submodule.span F (Set.range v)) := by rw [hspan, finrank_top]
        _ ≤ (Set.range v).toFinset.card := finrank_span_le_card _
        _ ≤ Fintype.card (P ⧸ Subgroup.center P) := by
            rw [Set.toFinset_range]; exact Finset.card_image_le.trans_eq Finset.card_univ
        _ = Nat.card (P ⧸ Subgroup.center P) := Nat.card_eq_fintype_card.symm
    rwa [Module.finrank_linearMap, ← pow_two] at hfr
  exact le_antisymm hle (card_quotient_center_le_sq_finrank ρ hf hcl)

end OddOrder.RepresentationTheory


