-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
-- name    : QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:30:58.18283+00:00
-- url     : https://prove2.me/theorems/62541f80-e962-48aa-b9d3-1c8b7e8fe06f
-- title:
--   Evaluation Shortening
-- statement:
--   Definitions and structural lemmas for Evaluation Shortening, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/EvaluationShortening.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationKernel
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_apply_eq_zero_of_not_mem

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k F ι J : Type*} [Field k] [Fintype k] [Field F] [Algebra k F]
variable [Fintype ι] [Fintype J]
theorem evaluationSupport_sub_of_not_range
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (p : J ↪ ι)
    (j : {j : ι // j ∉ Set.range p}) :
    (G - evaluationDivisor (fun a => Q (p a))) (Q j.val).place = 0 := by
  rw [Finsupp.sub_apply, hG j.val]
  have hz : evaluationDivisor (fun a => Q (p a)) (Q j.val).place = 0 := by
    apply zeroCoordinateDivisor_apply_eq_zero_of_not_mem
    intro a _ heq
    exact j.property ⟨a, hQ heq⟩
  rw [hz, sub_zero]
end
end QEC.Coding.AlgebraicGeometry


