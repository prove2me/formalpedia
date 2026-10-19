-- Prove2me | Definitions.Def_QAlgorithms_Defs_PurifiedDensityAccess
-- name    : QAlgorithms_Defs_PurifiedDensityAccess
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:44.453577+00:00
-- url     : https://prove2.me/theorems/b193aa93-7a26-418c-97b2-c3a835f4629a
-- title:
--   PurifiedDensityAccess
-- statement:
--   PurifiedDensityAccess
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\PurifiedDensityAccess.lean

import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_Measurement
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.QuantumEsscher

/-- QAlgorithms.QuantumEsscher.IsPurifiedAccess: arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.15. Source domains are explicit below. -/
def IsPurifiedAccess {a n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (O : Matrix (Qubits (a+n)) (Qubits (a+n)) ℂ) : Prop :=
  IsDensityMatrix rho ∧ O ∈ Matrix.unitaryGroup _ ℂ ∧
    traceLeft ((pureDensity (act O (zeroKet (a+n)))).submatrix
      (qubitsAppendEquiv a n).symm (qubitsAppendEquiv a n).symm) = rho

/-- QAlgorithms.QuantumEsscher.densityEncoding: arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.15. Source domains are explicit below. -/
def densityEncoding {a n : ℕ}
    (O : Matrix.unitaryGroup (Qubits (a+n)) ℂ) :
    Matrix (Qubits (a+n) × Qubits n) (Qubits (a+n) × Qubits n) ℂ :=
  let exchange : Matrix (Qubits (a+n) × Qubits n) (Qubits (a+n) × Qubits n) ℂ :=
    Matrix.of fun p q => if (qubitsAppendEquiv a n p.1).1 = (qubitsAppendEquiv a n q.1).1 ∧
      (qubitsAppendEquiv a n p.1).2 = q.2 ∧ p.2 = (qubitsAppendEquiv a n q.1).2 then 1 else 0
  Matrix.kronecker (star (O : Matrix _ _ ℂ)) 1*exchange*Matrix.kronecker (O : Matrix _ _ ℂ) 1

example {a n : ℕ} (O : Matrix.unitaryGroup (Qubits (a+n)) ℂ) :
    conjSuperop (densityEncoding O) 0 = 0 := by simp [conjSuperop]

end QAlgorithms.QuantumEsscher


