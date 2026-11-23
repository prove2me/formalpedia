-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
-- name    : GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:13.420799+00:00
-- url     : https://prove2.me/theorems/90e11c94-5b74-4f0b-9105-4d92e0201662
-- title:
--   Matrix Similarity
-- statement:
--   Definitions and structural lemmas for Matrix Similarity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
section Cyclic
variable {F : Type*} [Field F]
def monicAssoc (q : F[X]) : F[X] := q * C q.leadingCoeff⁻¹
theorem monicAssoc_monic {q : F[X]} (hq : q ≠ 0) : (monicAssoc q).Monic :=
  monic_mul_leadingCoeff_inv hq
theorem monicAssoc_dvd (q : F[X]) : monicAssoc q ∣ q := by
  by_cases hq : q = 0
  · simp [hq, monicAssoc]
  · refine ⟨C q.leadingCoeff, ?_⟩
    rw [monicAssoc, mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hq), C_1, mul_one]
def lcoeffMod (q f : F[X]) : F := (f %ₘ monicAssoc q).coeff (q.natDegree - 1)
theorem lcoeffMod_add (q f g : F[X]) : lcoeffMod q (f + g) = lcoeffMod q f + lcoeffMod q g := by
  simp [lcoeffMod, add_modByMonic]
theorem lcoeffMod_of_dvd {q f : F[X]} (hq : q ≠ 0) (h : q ∣ f) : lcoeffMod q f = 0 := by
  have : f %ₘ monicAssoc q = 0 :=
    (modByMonic_eq_zero_iff_dvd (monicAssoc_monic hq)).2 ((monicAssoc_dvd q).trans h)
  simp [lcoeffMod, this]
theorem lcoeffMod_eq_of_dvd_sub {q f g : F[X]} (hq : q ≠ 0) (h : q ∣ f - g) :
    lcoeffMod q f = lcoeffMod q g := by
  have e : f = (f - g) + g := by ring
  rw [e, lcoeffMod_add, lcoeffMod_of_dvd hq h, zero_add]
def ellQ (q : F[X]) (hq : q ≠ 0) : (F[X] ⧸ F[X] ∙ q) → F := fun a =>
  Quotient.liftOn' a (lcoeffMod q) (fun f g h => by
    have h' : f - g ∈ F[X] ∙ q := (Submodule.quotientRel_def _).1 h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h'
    exact lcoeffMod_eq_of_dvd_sub hq ⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩)
variable {q : F[X]} (hq : q ≠ 0)
end Cyclic
section Continuity
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
def ContCoeff {α : Type*} [TopologicalSpace α] (P : α → F[X]) : Prop :=
  ∀ k, Continuous fun a => (P a).coeff k
variable {α : Type*} [TopologicalSpace α]
omit [IsTopologicalRing F] in
theorem ContCoeff.C {f : α → F} (hf : Continuous f) : ContCoeff fun a => Polynomial.C (f a) :=
  fun k => by
    simp only [coeff_C]
    split_ifs
    · exact hf
    · exact continuous_const
variable {m : Type*} [Fintype m] [DecidableEq m]
end Continuity
section Decomposition
universe u
variable {F : Type u} [Field F] {n : ℕ}
end Decomposition
section SumForm
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → F[X])
  (hq : ∀ i, q i ≠ 0)
abbrev CycSum := DirectSum ι fun i => F[X] ⧸ F[X] ∙ q i
def sumForm (x y : CycSum q) : F := ∑ i, ellQ (q i) (hq i) (x i * y i)
end SumForm
section Gram
universe u
open scoped Matrix
variable {F : Type u} [Field F] {n : ℕ}
end Gram
section Countable
universe u
variable {F : Type u} [Field F] {n : ℕ}
end Countable
end GroundTheory.Automorphic.ContragredientTranspose


