-- Prove2me | Definitions.Def_FourierJacobi_Analysis_HaarLimits
-- name    : FourierJacobi_Analysis_HaarLimits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:37:59.106713+00:00
-- url     : https://prove2.me/theorems/ed5e916e-4b85-5a56-a09c-078898981939
-- title:
--   Haar Limits
-- statement:
--   Definitions and structural lemmas for Haar Limits, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean

import Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations FourierJacobi.Measure
open MeasureTheory Filter
open scoped Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
local notation "qK" => (residueCardinality K : ℝ)
end FourierJacobi.Analysis


