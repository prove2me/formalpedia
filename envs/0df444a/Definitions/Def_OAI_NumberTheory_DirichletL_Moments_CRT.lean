-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Moments_CRT
-- name    : OAI_NumberTheory_DirichletL_Moments_CRT
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:34:08.605901+00:00
-- url     : https://prove2.me/theorems/0d51b53c-bebd-45c4-ba72-d560edb04f83
-- title:
--   CRT
-- statement:
--   Definitions and structural lemmas for CRT, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/CRT.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Group.Pi.Units
set_option autoImplicit false
namespace OAI
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
def crtCharacter {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) :
    MulChar S ℂ where
  toFun x := ∏ i, χ i (e x i)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul, Finset.prod_mul_distrib]
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (e x) := fun h => hx ((isUnit_map_iff e x).mp h)
    have hsome : ∃ i, ¬IsUnit (e x i) := by
      by_contra h
      apply hn
      exact Pi.isUnit_iff.mpr (by simpa only [not_exists, not_not] using h)
    obtain ⟨i, hi⟩ := hsome
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((χ i).map_nonunit hi)
end
end SevenEighths.CenteredMomentCorrelation
end OAI


