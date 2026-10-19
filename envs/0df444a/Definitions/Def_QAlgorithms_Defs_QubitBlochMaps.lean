-- Prove2me | Definitions.Def_QAlgorithms_Defs_QubitBlochMaps
-- name    : QAlgorithms_Defs_QubitBlochMaps
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:00:20.059926+00:00
-- url     : https://prove2.me/theorems/7d1c0ad0-9096-4e4b-9153-eae419d07d63
-- title:
--   QubitBlochMaps
-- statement:
--   QubitBlochMaps
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\QubitBlochMaps.lean

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.QubitChannels

/-- The source's ordered Pauli basis X,Y,Z (0302032 p.2). -/
def sigma : Fin 3 → Matrix Bool Bool ℂ := ![pauliX,pauliY,pauliZ]

/-- Complex trace pairing on all operators (0302032 p.2, Pauli coordinates). -/
def tracePair (A : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ →ₗ[ℂ] ℂ where
  toFun X := (A*X).trace
  map_add' X Y := by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' a X := by simp [Matrix.mul_smul, Matrix.trace_smul]

/-- arxiv-quant-ph-0302032v3 PDF p.2; arxiv-quant-ph-0302032v3 PDF p.3. -/
def blochAffineMap (t : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ where
  toFun X := (X.trace/2) • (1+∑ j, (t j : ℂ) • sigma j) +
    ∑ j, ((∑ k, (M j k : ℂ)*(sigma k*X).trace)/2) • sigma j
  map_add' X Y := by
    simp [Matrix.trace_add, Matrix.mul_add, mul_add, Finset.sum_add_distrib, add_div, add_smul]
    abel
  map_smul' a X := by
    simp [Matrix.trace_smul, Matrix.mul_smul, Matrix.trace_smul, ← Finset.mul_sum,
      mul_div_assoc, mul_smul, Finset.smul_sum, mul_left_comm]

/-- arxiv-quant-ph-0302032v3 PDF p.2; arxiv-quant-ph-0302032v3 PDF p.3. -/
def HasCanonicalRepresentation (Phi : Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ)
    (t lam : Fin 3 → ℝ) : Prop :=
  ∃ U V : Matrix.unitaryGroup Bool ℂ, ∀ X,
    Phi X = conjSuperop (V : Matrix Bool Bool ℂ)
      (blochAffineMap t (Matrix.diagonal lam) (conjSuperop (U : Matrix Bool Bool ℂ) X))

/-- arxiv-quant-ph-0302032v3 PDF p.3; arxiv-quant-ph-0302032v3 PDF p.10; arxiv-quant-ph-0302032v3 PDF p.11. -/
def HasCanonicalSignChange (Phi : Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ) : Prop :=
  ∃ t lam : Fin 3 → ℝ, HasCanonicalRepresentation Phi t lam ∧
    ∀ j, Entanglement.IsCompletelyPositive
      (blochAffineMap t (Matrix.diagonal (Function.update lam j (-lam j))))

/-- Sanity check for the source model (arxiv-quant-ph-0302032v3 PDF p.2). -/
example (t : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) : blochAffineMap t M 0 = 0 := map_zero _

end QAlgorithms.QubitChannels


