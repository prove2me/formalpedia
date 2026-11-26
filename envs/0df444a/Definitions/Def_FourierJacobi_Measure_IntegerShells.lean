-- Prove2me | Definitions.Def_FourierJacobi_Measure_IntegerShells
-- name    : FourierJacobi_Measure_IntegerShells
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:41:04.021929+00:00
-- url     : https://prove2.me/theorems/83445793-5dc4-51ba-b2f4-0eb7cab22ba3
-- title:
--   Integer Shells
-- statement:
--   Definitions and structural lemmas for Integer Shells, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero


set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise WithZero
namespace FourierJacobi.Measure
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
local instance integerShells_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance
theorem canonical_uniformizer_ne_zero (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) : (π : K) ≠ 0 := by
  intro he
  rw [he, localFieldValuation_zero] at hπ
  exact WithTop.top_ne_coe hπ
def integerBall (n : ℤ) : Set K := {x | (n : WithTop ℤ) ≤ localFieldValuation K x}
def integerShell (n : ℤ) : Set K := {x | localFieldValuation K x = (n : WithTop ℤ)}
def canonicalUniformizerUnit (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) : Kˣ :=
  Units.mk0 (π : K) (canonical_uniformizer_ne_zero K π hπ)
variable [MeasurableSpace K] [BorelSpace K]
local instance integerShells_additiveHaar_regular : (additiveHaar K).Regular := by
  unfold additiveHaar
  infer_instance
end FourierJacobi.Measure


