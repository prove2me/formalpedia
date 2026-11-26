-- Prove2me | Definitions.Def_FourierJacobi_Analysis_HaarCellMaster
-- name    : FourierJacobi_Analysis_HaarCellMaster
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:36:22.204441+00:00
-- url     : https://prove2.me/theorems/f55b7e42-3cdf-4df3-98e9-04ab6414f933
-- title:
--   Haar Cell Master
-- statement:
--   Definitions and structural lemmas for Haar Cell Master, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMaster.lean

import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
import Definitions.Def_FourierJacobi_Analysis_HaarCellMass
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000
def haarCellScalarMass (q : ℝ) (r : ℤ) (i : LatticeIndex) : ℂ :=
  (1 - (q : ℂ)⁻¹) ^ 3 * ((q : ℂ) ^ (-i.2.1) * (q : ℂ) ^ (-i.2.2.1)) *
    collisionWeight (q : ℂ) r i.2.1 i.2.2.1 i.2.2.2
section LocalField
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
end LocalField
end FourierJacobi.Analysis


