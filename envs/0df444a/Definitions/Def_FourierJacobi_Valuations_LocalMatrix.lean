-- Prove2me | Definitions.Def_FourierJacobi_Valuations_LocalMatrix
-- name    : FourierJacobi_Valuations_LocalMatrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:27:46.449224+00:00
-- url     : https://prove2.me/theorems/913898fe-ef94-5517-b918-8aeca4d111dd
-- title:
--   Local Matrix
-- statement:
--   Definitions and structural lemmas for Local Matrix, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/LocalMatrix.lean

import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
import Definitions.Def_FourierJacobi_Measure_NullSets
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter FourierJacobi.LocalMatrix
namespace FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]
end FourierJacobi.Valuations


