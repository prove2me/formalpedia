-- Prove2me | Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness
-- name    : RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:35:12.738895+00:00
-- url     : https://prove2.me/theorems/6b579c71-eda7-423a-b80f-72368d998942
-- title:
--   Compactness
-- statement:
--   Definitions and structural lemmas for Compactness, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.UniformSpace.HeineCantor
set_option autoImplicit true
namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness
open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set
noncomputable section
section Volume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance instMeasurableSpaceEL2CompactnessCompactness : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessCompactness : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessCompactness : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddEL2CompactnessCompactness : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegEL2CompactnessCompactness : MeasurableNeg E := by
  infer_instance
variable {K : Set E}
variable {ψ : E → ℝ}
def Kψ : Set E :=
  K + tsupport ψ
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma isCompact_Kψ (hK : IsCompact K) (hψcs : HasCompactSupport ψ) :
    IsCompact (Kψ (K := K) (ψ := ψ)) :=
  IsCompact.add hK hψcs.isCompact
def smoothOn (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    C(↥(Kψ (K := K) (ψ := ψ)), ℝ) where
  toFun x := smoothFun (E := E) (K := K) ψ u x
  continuous_toFun := by
    have : Continuous (smoothFun (E := E) (K := K) ψ u) :=
      continuous_smoothFun (E := E) (K := K) (ψ := ψ) (hKm := hKm) hψc hψcs u
    exact this.comp continuous_subtype_val
def smoothBCF (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ :=
  letI : CompactSpace ↥(Kψ (K := K) (ψ := ψ)) :=
    isCompact_iff_compactSpace.1 (isCompact_Kψ (K := K) (ψ := ψ) hK hψcs)
  BoundedContinuousFunction.mkOfCompact (smoothOn (E := E) (K := K) (ψ := ψ) hKm hψc hψcs u)
end Volume
end
end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov


