-- Prove2me | Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
-- name    : QAlgorithms_Defs_EntanglementNegativity
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:58.541935+00:00
-- url     : https://prove2.me/theorems/346be284-c160-41f2-b407-fd719d2f1314
-- title:
--   EntanglementNegativity
-- statement:
--   EntanglementNegativity
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\EntanglementNegativity.lean

import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Entanglement

/-- arxiv-quant-ph-0102117v1 PDF p.1; arxiv-quant-ph-0102117v1 PDF p.2. -/
def negativity {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (X : Matrix (I × J) (I × J) ℂ) : ℝ := (traceNorm (partialTransposeFirst X)-1)/2

/-- Sanity check for the source model (arxiv-quant-ph-0102117v1 PDF p.1). -/
example {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    negativity (0 : Matrix (I × J) (I × J) ℂ) = -(1/2) := by
  have hz : partialTransposeFirst (0 : Matrix (I × J) (I × J) ℂ) = 0 := rfl
  rw [negativity,hz]
  norm_num [traceNorm,cfc_zero]

end QAlgorithms.Entanglement


