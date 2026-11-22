-- Prove2me | Definitions.Def_LeanPool_LatinQuarter_Tags
-- name    : LeanPool_LatinQuarter_Tags
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:07.582081+00:00
-- url     : https://prove2.me/theorems/5f2f7023-9fea-4481-98c4-16cbfd99cc63
-- title:
--   Tags
-- statement:
--   Definitions and structural lemmas for Tags, from Richard Bean; LeanPool contributors's pinned Critical sets in Latin squares development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Tags.lean

module
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Ideal
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LatinQuarter
open scoped BigOperators
open MvPolynomial
noncomputable def repeatedTagIdeal (κ : Type*) : Ideal (MvPolynomial κ (ZMod 2)) :=
  Ideal.span ((fun d => monomial d (1 : ZMod 2)) ''
    Set.range (fun j : κ => Finsupp.single j 2))
theorem squarefree_coeff_zero_of_mem {κ : Type*}
    {p : MvPolynomial κ (ZMod 2)} (hp : p ∈ repeatedTagIdeal κ)
    {d : κ →₀ ℕ} (hd : ∀ j, d j ≤ 1) : p.coeff d = 0 := by
  classical
  by_contra hn
  have hmem := mem_support_iff.mpr hn
  obtain ⟨e, ⟨j, rfl⟩, he⟩ := mem_ideal_span_monomial_image.mp hp d hmem
  have hj := he j
  simp only [Finsupp.single_eq_same] at hj
  have := hd j
  omega
theorem repeatedTagIdeal_ne_top (κ : Type*) : repeatedTagIdeal κ ≠ ⊤ := by
  intro h
  have hp : (1 : MvPolynomial κ (ZMod 2)) ∈ repeatedTagIdeal κ := by rw [h]; trivial
  have hz := squarefree_coeff_zero_of_mem hp (d := 0) (by simp)
  simp at hz
abbrev TagRing (κ : Type*) := MvPolynomial κ (ZMod 2) ⧸ repeatedTagIdeal κ
instance (κ : Type*) : Nontrivial (TagRing κ) :=
  Ideal.Quotient.nontrivial_iff.mpr (repeatedTagIdeal_ne_top κ)
instance (κ : Type*) : CharP (TagRing κ) 2 :=
  CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 2) (TagRing κ)) 2 (by decide)
noncomputable def tag {κ : Type*} (j : κ) : TagRing κ :=
  Ideal.Quotient.mk _ (X j)
noncomputable def allTagsExponent (κ : Type*) [Fintype κ] : κ →₀ ℕ :=
  ∑ j : κ, Finsupp.single j 1
end LatinQuarter


