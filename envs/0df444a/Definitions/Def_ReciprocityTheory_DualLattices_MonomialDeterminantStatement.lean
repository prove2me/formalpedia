-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_MonomialDeterminantStatement
-- name    : ReciprocityTheory_DualLattices_MonomialDeterminantStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:29.129863+00:00
-- url     : https://prove2.me/theorems/ce739cb9-3a00-4c9d-bfd8-e2c3832b9012
-- title:
--   Monomial Determinant Statement
-- statement:
--   Definitions and structural lemmas for Monomial Determinant Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MonomialDeterminantStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
def MonomialDeterminantStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal) (R : Type)
    [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R) (u : ι → (ι → ZMod p) → C),
    IsUnit Λ.det → (∀ j x, v (u j x) ≤ 1) →
    (∀ j x, v (u j x - algebraMap R C (∑ i, Λ j i * ((x i).val : R))) < 1) →
    v (Matrix.of fun (x α : ι → ZMod p) => ∏ j, u j x ^ (α j).val).det = 1 ∧
    ∀ ε : ι → C,
      v (Matrix.of fun (x α : ι → ZMod p) => ∏ j, (ε j * u j x) ^ (α j).val).det =
        ∏ j, v (ε j) ^ (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2))
end ReciprocityTheory.PGsh.Up


