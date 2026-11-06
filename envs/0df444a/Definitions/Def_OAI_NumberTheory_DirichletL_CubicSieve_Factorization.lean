-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Factorization
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_Factorization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:44.123918+00:00
-- url     : https://prove2.me/theorems/549be711-b5ae-4cd5-b708-7fb3dbfcf7f4
-- title:
--   Factorization
-- statement:
--   Definitions and structural lemmas for Factorization, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/Factorization.lean

import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace OAI
namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section
variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]
def firstPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 1), p
def secondPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 2), p
def cubePart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset, p ^ ((normalizedFactors x).count p / 3)
end
end SevenEighths.CubicSieve
end OAI


