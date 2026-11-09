-- Prove2me | Definitions.Def_QMCLeafB_wMatrixQ
-- name    : QMCLeafB_wMatrixQ
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-08T19:21:28.652024+00:00
-- url     : https://prove2.me/theorems/ef0bd401-afbf-4fda-86b5-30c19fa24681
-- title:
--   Rational weight matrix
-- statement:
--   Rational symmetric weight matrix $A(G)_{ij}=w_{ij}$ with zero diagonal.
-- source:
--   QMC leaf B, local bricks

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

open scoped BigOperators

namespace QMCLeafB

/-- Rational weight matrix -/
noncomputable def wMatrixQ (G : QuantumMaxCutEnergy.Input) : Matrix (Fin G.n) (Fin G.n) ℚ :=
  Matrix.of fun i j => if h : i < j then ((G.weights ⟨(i, j), h⟩ : ℚ≥0) : ℚ) else if h : j < i then ((G.weights ⟨(j, i), h⟩ : ℚ≥0) : ℚ) else 0

end QMCLeafB


