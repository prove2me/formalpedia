-- Prove2me | Definitions.Def_FourierJacobi_Analysis_HaarCellMass
-- name    : FourierJacobi_Analysis_HaarCellMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:35:32.033947+00:00
-- url     : https://prove2.me/theorems/e6401cba-b808-5607-9a42-4d667d3cbfca
-- title:
--   Haar Cell Mass
-- statement:
--   Definitions and structural lemmas for Haar Cell Mass, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCellMass.lean

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Measure_JointCollision
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace FourierJacobi.Analysis
open FourierJacobi.Measure FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
def haarCellWeight (r j h : ℤ) (c : ℕ) : ℝ :=
  if r = 0 ∨ 2 * h ≠ j - r then (if c = 0 then 1 else 0)
  else shellCollisionProbability K c
variable [MeasurableSpace K] [BorelSpace K]
local instance haarCellMass_t2Space : T2Space K := kernelField_t2Space K
local instance haarCellMass_secondCountable : SecondCountableTopology K := kernelField_secondCountable K
local instance haarCellMass_unitsBorel : BorelSpace Kˣ := coreUnits_borelSpace K
local instance haarCellMass_additiveSigmaFinite : SigmaFinite (additiveHaar K) := by
  unfold additiveHaar
  infer_instance
def paperCoreMeasure : MeasureTheory.Measure (HaarPoint K) :=
  (paperMultiplicativeHaar K).prod ((additiveHaar K).prod (additiveHaar K))
end FourierJacobi.Analysis


