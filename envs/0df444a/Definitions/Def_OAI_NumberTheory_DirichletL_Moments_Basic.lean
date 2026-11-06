-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Basic
-- name    : OAI_NumberTheory_DirichletL_Moments_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:10.531585+00:00
-- url     : https://prove2.me/theorems/713d59dc-7e81-43cc-8849-6aa2d9652a21
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Basic.lean

import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Group.Commute.Units
set_option autoImplicit false
namespace OAI
open scoped BigOperators NNReal
namespace SevenEighths.CenteredMoment
noncomputable section
variable {M R : Type*} [CommMonoid M] [CommRing R]
structure MaskedCharacter (M R : Type*) [CommMonoid M] [CommRing R] where
  residue : M →* R
  character : MulChar R ℂ
  keep : M → Prop
  keep_mul : ∀ a b, keep (a * b) ↔ keep a ∧ keep b
def ofResidueMask {S : Type*} [CommRing S] (ρ : M →* R)
    (χ : MulChar R ℂ) (puncture : M →* S) : MaskedCharacter M R where
  residue := ρ
  character := χ
  keep a := IsUnit (puncture a)
  keep_mul a b := by
    rw [map_mul]
    exact (Commute.all _ _).isUnit_mul_iff
def MaskedCharacter.value (d : MaskedCharacter M R) (a : M) : ℂ :=
  @ite ℂ (d.keep a) (Classical.propDecidable _) (d.character (d.residue a)) 0
def normTwist (N : M →* ℝ≥0) (t : ℝ) (a : M) : ℂ :=
  ((N a : ℝ) : ℂ) ^ (Complex.I * t)
def coefficient (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ) (a : M) : ℂ :=
  d.value a * normTwist N t a
def plainSum (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (s : Finset M) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ a ∈ s, coefficient d N t a * W ((N a : ℝ) / X)
def rectangle (N : M →* ℝ≥0) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (a b : M) : ℂ :=
  W₁ ((N a : ℝ) / X₁) * W₂ ((N b : ℝ) / X₂) -
    W₁ ((N a : ℝ) / Y₁) * W₂ ((N b : ℝ) / Y₂)
def volumeTerm (c I : ℂ) (t X : ℝ) : ℂ :=
  c * (X : ℂ) ^ (1 + Complex.I * t) * I
end
end SevenEighths.CenteredMoment
end OAI


