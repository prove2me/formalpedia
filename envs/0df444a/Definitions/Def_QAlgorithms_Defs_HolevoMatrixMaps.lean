-- Prove2me | Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
-- name    : QAlgorithms_Defs_HolevoMatrixMaps
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:39:18.266337+00:00
-- url     : https://prove2.me/theorems/d052d1eb-fd93-449e-93d7-890bfe428f48
-- title:
--   HolevoMatrixMaps
-- statement:
--   HolevoMatrixMaps
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\HolevoMatrixMaps.lean

import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Entanglement

/-- arxiv-quant-ph-0302031v2 PDF p.2; arxiv-quant-ph-0302031v2 PDF p.4; arxiv-quant-ph-0302032v3 PDF p.2; arxiv-quant-ph-0302032v3 PDF p.3. -/
def holevoMap {K I J : Type*} [Fintype K] [Fintype I]
    (R : K → Matrix J J ℂ) (F : K → Matrix I I ℂ) : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ where
  toFun X := ∑ k, (F k * X).trace • R k
  map_add' X Y := by simp [Matrix.mul_add, Matrix.trace_add, add_smul, Finset.sum_add_distrib]
  map_smul' a X := by simp [Matrix.mul_smul, Matrix.trace_smul, mul_smul, Finset.smul_sum]

/-- arxiv-quant-ph-0302032v3 PDF p.2; arxiv-quant-ph-0302032v3 PDF p.3. -/
def HasHolevoPOVMForm (Phi : Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ) : Prop :=
  ∃ q : ℕ, ∃ R F : Fin q → Matrix Bool Bool ℂ,
    (∀ k, IsDensityMatrix (R k)) ∧ IsPOVM F ∧ Phi = holevoMap R F

/-- arxiv-quant-ph-0302032v3 PDF p.2; arxiv-quant-ph-0302032v3 PDF p.6; arxiv-quant-ph-0302032v3 PDF p.11; arxiv-quant-ph-0302032v3 PDF p.12. -/
def IsCQMap (Phi : Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ) : Prop :=
  ∃ U : Matrix.unitaryGroup Bool ℂ, ∃ R : Bool → Matrix Bool Bool ℂ,
    (∀ b, IsDensityMatrix (R b)) ∧
    Phi = holevoMap R (fun b => pureDensity (act (U : Matrix Bool Bool ℂ) (ket b)))

/-- Sanity check for the source model (arxiv-quant-ph-0302031v2 PDF p.2). -/
example {K I J : Type*} [Fintype K] [Fintype I]
    (R : K → Matrix J J ℂ) (F : K → Matrix I I ℂ) : holevoMap R F 0 = 0 := map_zero _

end QAlgorithms.Entanglement


