-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BurnsideBasis
-- name    : OddOrder_GroupTheory_RepresentationTheory_BurnsideBasis
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:52:04.707207+00:00
-- url     : https://prove2.me/theorems/b57ef422-7927-4cdb-8a8b-6beec804ca2f
-- title:
--   The Burnside basis of $\mathrm{End}_F V$ (BG (2.11))
-- statement:
--   A shared module exposing the Burnside basis used in (2.11) of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*: for a faithful irreducible representation $\rho$ of a finite group $P$ of nilpotency class at most 2 over an algebraically closed field with characteristic not dividing $|P|$, the images $\rho(\mathrm{out}\,c)$ of a transversal of the central cosets form a basis of $\mathrm{End}_F V$ (spanning plus linear independence).
--
--   Main declarations: `burnsideBasisOfSection`; `burnsideBasis` (The Burnside basis (BG (2.11)) at the canonical section `Quotient.out`).
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/BurnsideBasis.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/BurnsideBasis.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtraspecialFaithful

namespace OddOrder.RepresentationTheory

open Representation Module

variable {F : Type*} [Field F] [IsAlgClosed F]

variable {P : Type*} [Group P] {V : Type*} [AddCommGroup V] [Module F V]

/-- **Linear independence of central-coset images, for any section** (BG (2.11), independence half).
For any section `t` of `P ↠ P/Z(P)` (`⟦t c⟧ = c`), the family `c ↦ ρ(t c)` is `F`-linearly
independent in `End_F V`: pairing `A ↦ trace(A · ρ(t c')⁻¹)` gives the diagonal Gram matrix
`χ(t c · (t c')⁻¹) = δ_{c c'} · (dim V)`, nonsingular since `(dim V : F) ≠ 0`. -/
theorem linearIndependent_representation_section [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P)
    (t : P ⧸ Subgroup.center P → P) (ht : ∀ c, (↑(t c) : P ⧸ Subgroup.center P) = c) :
    LinearIndependent F (fun c : P ⧸ Subgroup.center P => ρ (t c)) := by
  classical
  have : Fintype P := Fintype.ofFinite P
  have : Fintype (P ⧸ Subgroup.center P) := Fintype.ofFinite _
  have hmem : ∀ c c' : P ⧸ Subgroup.center P,
      t c * (t c')⁻¹ ∈ Subgroup.center P ↔ c = c' := by
    intro c c'
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ht, ht]
    exact mul_inv_eq_one
  have hTval : ∀ c c' : P ⧸ Subgroup.center P,
      LinearMap.trace F V (ρ (t c) * ρ ((t c')⁻¹))
        = if c = c' then (Module.finrank F V : F) else 0 := by
    intro c c'
    rw [← map_mul]
    change ρ.character _ = _
    by_cases h : c = c'
    · subst h; rw [if_pos rfl, mul_inv_cancel, char_one]
    · rw [if_neg h]
      exact character_eq_zero_of_notMem_center ρ hf hcl ((hmem c c').not.mpr h)
  rw [Fintype.linearIndependent_iff]
  intro coef hcoef j
  have happ : LinearMap.trace F V
        ((∑ i, coef i • ρ (t i)) * ρ ((t j)⁻¹))
      = ∑ i, coef i • LinearMap.trace F V (ρ (t i) * ρ ((t j)⁻¹)) := by
    rw [Finset.sum_mul, map_sum]
    simp only [smul_mul_assoc, map_smul]
  rw [hcoef, zero_mul, map_zero] at happ
  simp only [hTval, smul_ite, smul_zero] at happ
  rw [Finset.sum_ite_eq' Finset.univ j] at happ
  simp only [Finset.mem_univ, if_true, smul_eq_mul] at happ
  exact (mul_eq_zero.mp happ.symm).resolve_right (finrank_cast_ne_zero ρ hf hcl)

/-- **Spanning of central-coset images, for any section** (BG (2.11), Burnside spanning half). For
any section `t` of `P ↠ P/Z(P)`, the images `{ρ(t c)}` span `End_F V`: by Burnside `{ρ g}` spans,
and each `ρ g` is the central-character multiple `s · ρ(t ⟦g⟧)`. -/
theorem span_range_section_eq_top [FiniteDimensional F V] (ρ : Representation F P V)
    [ρ.IsIrreducible] (t : P ⧸ Subgroup.center P → P)
    (ht : ∀ c, (↑(t c) : P ⧸ Subgroup.center P) = c) :
    Submodule.span F (Set.range fun c : P ⧸ Subgroup.center P => ρ (t c)) = ⊤ := by
  set v : (P ⧸ Subgroup.center P) → Module.End F V := fun c => ρ (t c) with hv
  have hmem_span : ∀ g : P, ρ g ∈ Submodule.span F (Set.range v) := by
    intro g
    have hz : g * (t (↑g : P ⧸ Subgroup.center P))⁻¹ ∈ Subgroup.center P := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ht]
      exact mul_inv_cancel _
    obtain ⟨s, hs⟩ := center_isScalar ρ hz
    have hgeq : g = g * (t (↑g : P ⧸ Subgroup.center P))⁻¹ * t (↑g : P ⧸ Subgroup.center P) := by
      group
    rw [hgeq, map_mul, hs, ← Module.End.one_eq_id, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ s (Submodule.subset_span (Set.mem_range_self _))
  have hsub : ∀ r : MonoidAlgebra F P, ρ.asAlgebraHom r ∈ Submodule.span F (Set.range v) := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of g => rw [asAlgebraHom_of]; exact hmem_span g
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro A _
  obtain ⟨r, rfl⟩ := asAlgebraHom_surjective_of_isAlgClosed ρ A
  exact hsub r

/-- **The Burnside basis, for any section** (BG (2.11)): for a faithful irreducible representation
of a finite group `P` of nilpotency class `≤ 2` over an algebraically closed field
(`char ∤ |P|`), and any section `t` of `P ↠ P/Z(P)`, the images `{ρ(t c) : c ∈ P/Z(P)}` form a
basis of `End_F V`.
(With a `φ`-equivariant section, the conjugation action on this basis is a *pure permutation* —
the input to the BG (2.11) `F[H]`-module structure.) -/
noncomputable def burnsideBasisOfSection [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P)
    (t : P ⧸ Subgroup.center P → P) (ht : ∀ c, (↑(t c) : P ⧸ Subgroup.center P) = c) :
    Basis (P ⧸ Subgroup.center P) F (Module.End F V) :=
  Basis.mk (linearIndependent_representation_section ρ hf hcl t ht)
    (span_range_section_eq_top ρ t ht).ge

@[simp]
theorem burnsideBasisOfSection_apply [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P)
    (t : P ⧸ Subgroup.center P → P) (ht : ∀ c, (↑(t c) : P ⧸ Subgroup.center P) = c)
    (c : P ⧸ Subgroup.center P) :
    burnsideBasisOfSection ρ hf hcl t ht c = ρ (t c) :=
  Basis.mk_apply _ _ c

/-- **The Burnside basis** (BG (2.11)) at the canonical section `Quotient.out`. -/
noncomputable def burnsideBasis [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P) :
    Basis (P ⧸ Subgroup.center P) F (Module.End F V) :=
  burnsideBasisOfSection ρ hf hcl Quotient.out (fun c => Quotient.out_eq' c)

@[simp]
theorem burnsideBasis_apply [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P)
    (c : P ⧸ Subgroup.center P) :
    burnsideBasis ρ hf hcl c = ρ (Quotient.out c) :=
  burnsideBasisOfSection_apply ρ hf hcl Quotient.out _ c

end OddOrder.RepresentationTheory


