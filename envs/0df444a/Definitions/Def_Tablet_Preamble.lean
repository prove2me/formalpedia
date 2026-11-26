-- Prove2me | Definitions.Def_Tablet_Preamble
-- name    : Tablet_Preamble
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:47:09.237787+00:00
-- url     : https://prove2.me/theorems/e15b5fe8-1443-50d0-86a7-fa3cc7d2d0ab
-- title:
--   Preamble
-- statement:
--   Definitions and structural lemmas for Preamble, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/Preamble.lean

import Mathlib.Analysis.ConstantSpeed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
set_option autoImplicit false


