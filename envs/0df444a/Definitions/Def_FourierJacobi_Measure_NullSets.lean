-- Prove2me | Definitions.Def_FourierJacobi_Measure_NullSets
-- name    : FourierJacobi_Measure_NullSets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:27:37.83936+00:00
-- url     : https://prove2.me/theorems/0d070bc8-b559-440d-93a0-7751e31ad995
-- title:
--   Null Sets
-- statement:
--   Definitions and structural lemmas for Null Sets, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean

import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
namespace FourierJacobi.Measure
section LocalField
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
end LocalField
section PolynomialNullSets
variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [SecondCountableTopology K]
  [T2Space K] [MeasurableSpace K] [BorelSpace K]
  (μ ν : MeasureTheory.Measure K) [NullSingletonClass ν]
variable [NullSingletonClass μ]
end PolynomialNullSets
section LocalHaarApplication
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]
end LocalHaarApplication
end FourierJacobi.Measure


