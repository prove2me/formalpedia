-- Prove2me | Definitions.Def_FourierJacobi_Measure_UnitScaling
-- name    : FourierJacobi_Measure_UnitScaling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:52:59.763899+00:00
-- url     : https://prove2.me/theorems/bfdadb31-9a1b-5dfa-9058-8a5773fc6196
-- title:
--   Unit Scaling
-- statement:
--   Definitions and structural lemmas for Unit Scaling, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/UnitScaling.lean

import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise
namespace FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
local instance unitScaling_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance
variable [MeasurableSpace K] [BorelSpace K]
local instance unitScaling_additiveHaar_regular : (additiveHaar K).Regular := by
  unfold additiveHaar
  infer_instance
end FourierJacobi.Measure


