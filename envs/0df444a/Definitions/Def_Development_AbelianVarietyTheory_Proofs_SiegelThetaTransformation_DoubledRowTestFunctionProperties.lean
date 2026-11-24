-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledRowTestFunctionProperties
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledRowTestFunctionProperties
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:58.733696+00:00
-- url     : https://prove2.me/theorems/e35a796d-74c4-4a46-b56b-b80444a2bfc4
-- title:
--   Doubled Row Test Function Properties
-- statement:
--   Definitions and structural lemmas for Doubled Row Test Function Properties, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real Kronecker
namespace GlobalTheory.Phase.Doubling
noncomputable section
variable {n g : ℕ}
def rowM (j : Fin 2) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) : Matrix (Fin n) (Fin g) ℚ :=
  Matrix.of fun k i => x j (k, i)
def glue (a b : Matrix (Fin n) (Fin g) ℚ) : Matrix (Fin 2) (Fin n × Fin g) ℚ :=
  Matrix.of fun j p => if j = 0 then a p.1 p.2 else b p.1 p.2
theorem rowM_glue_zero (a b : Matrix (Fin n) (Fin g) ℚ) : rowM 0 (glue a b) = a := by
  ext k i; simp [rowM, glue]
theorem rowM_glue_one (a b : Matrix (Fin n) (Fin g) ℚ) : rowM 1 (glue a b) = b := by
  ext k i; simp [rowM, glue]
theorem glue_rowM (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) : glue (rowM 0 x) (rowM 1 x) = x := by
  ext j p; fin_cases j <;> simp [rowM, glue]
def rowEquiv (n g : ℕ) : Matrix (Fin 2) (Fin n × Fin g) ℚ ≃
    Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ where
  toFun x := (rowM 0 x, rowM 1 x)
  invFun p := glue p.1 p.2
  left_inv x := glue_rowM x
  right_inv p := by simp [rowM_glue_zero, rowM_glue_one]
def comp (j : Fin 2) : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ →+
    Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ where
  toFun y := (rowM j y.1, rowM j y.2)
  map_zero' := rfl
  map_add' _ _ := rfl
def glueP : (Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) ×
    (Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) →+
    Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ where
  toFun z := (glue z.1.1 z.2.1, glue z.1.2 z.2.2)
  map_zero' := by
    refine Prod.ext ?_ ?_ <;> ext j p <;> simp [glue]
  map_add' a b := by
    refine Prod.ext ?_ ?_ <;> ext j p <;> fin_cases j <;> simp [glue]
end
end GlobalTheory.Phase.Doubling


