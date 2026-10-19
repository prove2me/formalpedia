-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapA09_Model
-- name    : QAlgorithms_Papers_RoadmapA09_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:31:06.553365+00:00
-- url     : https://prove2.me/theorems/9a40a72a-d2e4-4f9f-b0c8-66b0452adb0d
-- title:
--   The Quantum Esscher Transform: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   The Quantum Esscher Transform, arXiv:2401.07561v2, https://arxiv.org/abs/2401.07561v2. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_EsscherOracleCircuits
noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.RoadmapA09

open QAlgorithms.QuantumEsscher

/-- Proposition 12, arXiv:2401.07561v2, PDF p.15: the density signal obtained from
purified access, flattened with purification ancillas first and the signal system last.
This only reindexes the frozen `densityEncoding`; it introduces no accuracy assumption. -/
def purifiedDensitySignal (P : PublicParameters)
    (purification : Matrix.unitaryGroup (Qubits (P.purificationAncillas + P.n)) ℂ) :
    Matrix (Qubits (externalWidths P 0)) (Qubits (externalWidths P 0)) ℂ :=
  castOperator (by simp [externalWidths]; omega)
    ((densityEncoding purification).submatrix
      (qubitsAppendEquiv (P.purificationAncillas + P.n) P.n)
      (qubitsAppendEquiv (P.purificationAncillas + P.n) P.n))


end QAlgorithms.Papers.RoadmapA09


