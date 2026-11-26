-- Prove2me | Definitions.Def_FourierJacobi_Analysis_HaarCellValue
-- name    : FourierJacobi_Analysis_HaarCellValue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:35:30.730179+00:00
-- url     : https://prove2.me/theorems/b031c9ab-cd24-5d3a-a308-c5386b55e8ff
-- title:
--   Haar Cell Value
-- statement:
--   Definitions and structural lemmas for Haar Cell Value, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellValue.lean

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000
def haarCellValue (q : ℝ) (a b d : ℂ) (T : ℝ) (r : ℤ) (i : LatticeIndex) : ℂ :=
  d ^ i.1 * (Real.rpow (q ^ (-i.1)) (3 / 2) : ℂ) *
    (T : ℂ) ^ (-entryMinimum r i.1 i.2.1 i.2.2.1) *
      weylKernelAtIndices (inverseSqrt q : ℂ) a b
        ((cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).1 / 2)
        (cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).2
section LocalField
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
end LocalField
end FourierJacobi.Analysis


