-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:47:15.110521+00:00
-- url     : https://prove2.me/theorems/68f3590c-59ac-4afe-bd36-b54cef23c535
-- title:
--   Normal Closure Input
-- statement:
--   Definitions and structural lemmas for Normal Closure Input, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureInput.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationCode_one_mem
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationCode_starSquare_le_dual
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_selected_eq_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationPivot_evaluation_surjective

set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
def f256SourceInput (i : ℕ) : SourceInput F256 (Fin (f256GarciaStichtenothLength i))
    (Fin (f256MultiplicationLogicalCount i)) where
  code := f256MultiplicationCode i
  pivotEmbedding := f256MultiplicationPivot i
  pivotRestrict_surjective := by
    intro u
    obtain ⟨f, hf⟩ := f256MultiplicationPivot_evaluation_surjective i u
    refine ⟨⟨agEvaluationLinearMap (f256MultiplicationDivisor i)
      (f256GarciaStichtenothSelectedRationalPlace i)
      (f256MultiplicationDivisor_selected_eq_zero i) f, ⟨f, rfl⟩⟩, hf⟩
  one_mem_code := f256MultiplicationCode_one_mem i
  starSquare_le_dual := f256MultiplicationCode_starSquare_le_dual i
end QEC.Distillation.Ngu24MultiplicativeCSS
end


