-- Prove2me | Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
-- name    : QAlgorithms_Defs_MatrixMapPositivity
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:38:04.935234+00:00
-- url     : https://prove2.me/theorems/4abc462c-b0c9-4d34-a90e-70a114670004
-- title:
--   MatrixMapPositivity
-- statement:
--   MatrixMapPositivity
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MatrixMapPositivity.lean

import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Entanglement

/-- arxiv-quant-ph-0302032v3 PDF p.2; arxiv-quant-ph-0302032v3 PDF p.3; arxiv-quant-ph-0302032v3 PDF p.8. -/
def IsCompletelyPositive {I J : Type*} [Fintype I] [Fintype J]
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Prop :=
  ∀ r : ℕ, ∀ X : Matrix (Fin r × I) (Fin r × I) ℂ,
    X.PosSemidef → (idTensorSuperop Phi X).PosSemidef

/-- Sanity check for the source model (arxiv-quant-ph-0302032v3 PDF p.2). -/
example {I J : Type*} [Fintype I] [Fintype J] :
    IsCompletelyPositive (0 : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) := by
  intro r X _
  have h : idTensorSuperop (0 : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) X = 0 := rfl
  rw [h]
  exact Matrix.PosSemidef.zero

end QAlgorithms.Entanglement


