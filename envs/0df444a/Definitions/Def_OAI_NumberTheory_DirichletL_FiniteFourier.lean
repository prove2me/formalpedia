-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
-- name    : OAI_NumberTheory_DirichletL_FiniteFourier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:10.117205+00:00
-- url     : https://prove2.me/theorems/520f4278-df1b-49c4-9764-a7a86dc1076a
-- title:
--   Finite Fourier
-- statement:
--   Definitions and structural lemmas for Finite Fourier, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean

import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra
set_option autoImplicit false
namespace OAI
open scoped BigOperators
namespace SevenEighths.FiniteFourier
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]
def IsPrimitiveOnIdeals (χ : MulChar R ℂ) : Prop :=
  ∀ I : Ideal R, I ≠ ⊥ → ∃ u : Rˣ, (u : R) - 1 ∈ I ∧ χ (u : R) ≠ 1
def transform (ψ : AddChar R ℂ) (f : R → ℂ) (a : R) : ℂ :=
  ∑ x : R, f x * ψ (a * x)
end
end SevenEighths.FiniteFourier
end OAI


