-- Prove2me | Definitions.Def_QEC_Semantics_Channels_Choi
-- name    : QEC_Semantics_Channels_Choi
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:47:30.37952+00:00
-- url     : https://prove2.me/theorems/d89cff28-ab93-448c-90bf-8d78dad438b4
-- title:
--   Choi
-- statement:
--   Definitions and structural lemmas for Choi, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Choi.lean

import Definitions.Def_QEC_Semantics_Channels_Core
set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder
namespace OperatorMatrix
variable {n : Nat} {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
noncomputable def matrixUnit (b : OrthonormalBasis (Fin n) Complex H) (i j : Fin n) :
    Operator H :=
  (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap
noncomputable def matrixUnitBlock (b : OrthonormalBasis (Fin n) Complex H) :
    OperatorMatrix n H :=
  fun i j => matrixUnit b i j
end OperatorMatrix
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
noncomputable def choiMatrix {n : Nat} {βK : Type*} [Fintype βK]
    (Φ : Operator H →ₗ[Complex] Operator K)
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis βK Complex K) :
    Matrix (Fin n × βK) (Fin n × βK) Complex :=
  OperatorMatrix.scalarMatrix
    (OperatorMatrix.map Φ (OperatorMatrix.matrixUnitBlock bH)) bK
noncomputable def stdChoiMatrix (Φ : Operator H →ₗ[Complex] Operator K) :
    Matrix
      (Fin (Module.finrank Complex H) × Fin (Module.finrank Complex K))
      (Fin (Module.finrank Complex H) × Fin (Module.finrank Complex K)) Complex :=
  choiMatrix Φ (stdOrthonormalBasis Complex H) (stdOrthonormalBasis Complex K)
end Semantics
end QEC


