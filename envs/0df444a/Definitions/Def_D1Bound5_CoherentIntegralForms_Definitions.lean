-- Prove2me | Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
-- name    : D1Bound5_CoherentIntegralForms_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:31:05.678631+00:00
-- url     : https://prove2.me/theorems/da1ae8a1-e43c-45f3-8d2c-c5809acc934f
-- title:
--   Coherent Integral Forms
-- statement:
--   The terminal root with the branch fixed by the analytic construction. The named objects in this bundle include `coherentTerminalRoot`, `coherentAnchorRoot`.
-- source:
--   D1Bound5/CoherentIntegralForms.lean, lines 10-12, SHA-256 81e6a044e834ea1f7a20cfce931dfefd9cdd8cbc6a1dc7467c69328d64c38e4c; D1Bound5/CoherentIntegralForms.lean, lines 14-17, SHA-256 81e6a044e834ea1f7a20cfce931dfefd9cdd8cbc6a1dc7467c69328d64c38e4c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- The terminal root with the branch fixed by the analytic construction. -/
noncomputable def coherentTerminalRoot (p q eta : ℂ) : ℂ :=
  eta * ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ))

/-- The anchor root with the same coherent analytic branch choices. -/
noncomputable def coherentAnchorRoot (a p q eta : ℂ) : ℂ :=
  a * eta * ((1 + p⁻¹ * a⁻¹) ^ (1 / 2 : ℂ)) *
    ((1 + q⁻¹ * a⁻¹) ^ (1 / 2 : ℂ))











end D1Bound5
end


