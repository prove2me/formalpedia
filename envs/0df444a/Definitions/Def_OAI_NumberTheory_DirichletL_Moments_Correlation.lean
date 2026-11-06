-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
-- name    : OAI_NumberTheory_DirichletL_Moments_Correlation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:05.21727+00:00
-- url     : https://prove2.me/theorems/8262d537-92e6-4b1a-8d81-ca85c59960f5
-- title:
--   Correlation
-- statement:
--   Definitions and structural lemmas for Correlation, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Correlation.lean

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
set_option autoImplicit false
namespace OAI
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
def fourierSum (ψ : AddChar R ℂ) (place : X → R) (f : X → ℂ) (h : R) : ℂ :=
  ∑ x, f x * ψ (h * place x)
def fullCorrelation (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (j : R) : ℂ :=
  ∑ x, ∑ y, if left x - right y = j then f x * star (g y) else 0
section FiniteField
variable {F : Type*} [Field F] [Fintype F]
def shiftCorrelation (χ : MulChar F ℂ) (k : F) : ℂ :=
  ∑ x : F, χ x * star (χ (x - k))
def localCorrelation (χ : MulChar F ℂ) (n₁ n₂ k : F) : ℂ :=
  fullCorrelation (fun x : F => n₂ * x) (fun y : F => n₁ * y) χ χ k
end FiniteField
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
def reductionMultiplicity (π : A →+* B) : ℕ :=
  (Finset.univ.filter fun x : A => π x = 0).card
end
end SevenEighths.CenteredMomentCorrelation
end OAI


