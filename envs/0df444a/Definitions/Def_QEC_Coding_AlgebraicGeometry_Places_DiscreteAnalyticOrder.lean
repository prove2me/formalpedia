-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
-- name    : QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:02:02.513503+00:00
-- url     : https://prove2.me/theorems/ebebaa98-14f7-4f5c-8b2a-cbd541a43830
-- title:
--   Discrete Analytic Order
-- statement:
--   Definitions and structural lemmas for Discrete Analytic Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)
end
end QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder


