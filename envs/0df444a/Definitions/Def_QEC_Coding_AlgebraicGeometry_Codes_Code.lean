-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
-- name    : QEC_Coding_AlgebraicGeometry_Codes_Code
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:22:44.947341+00:00
-- url     : https://prove2.me/theorems/d44534c1-6745-481d-b1c9-9b6193173035
-- title:
--   Code
-- statement:
--   Definitions and structural lemmas for Code, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Code.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]
def agWordStar (x y : Word k ι) : Word k ι := fun i => x i * y i
def agStarProduct [Fintype k] (C D : LinearCode k ι) :
    Submodule k (Word k ι) :=
  Submodule.span k {w | ∃ x ∈ C.carrier, ∃ y ∈ D.carrier, agWordStar x y = w}
theorem evaluationSupport_add (G H : Divisor (GlobalPlace k F))
    (Q : ι → RationalPlace k F) (hG : ∀ i, G (Q i).place = 0)
    (hH : ∀ i, H (Q i).place = 0) :
    ∀ i, (G + H) (Q i).place = 0 := by
  intro i
  rw [Finsupp.add_apply, hG i, hH i]
  rfl
end QEC.Coding.AlgebraicGeometry


