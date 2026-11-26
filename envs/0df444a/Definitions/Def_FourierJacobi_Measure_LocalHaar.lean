-- Prove2me | Definitions.Def_FourierJacobi_Measure_LocalHaar
-- name    : FourierJacobi_Measure_LocalHaar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:40:40.512862+00:00
-- url     : https://prove2.me/theorems/3a478b58-0ab1-4e96-8283-68c42f3bc335
-- title:
--   Local Haar
-- statement:
--   Definitions and structural lemmas for Local Haar, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Theorems.Thm_FourierJacobi_Measure_localField_haar_nullSingletonClass
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero


set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open scoped ENNReal NNReal
namespace FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
local instance localField_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance
variable [MeasurableSpace K] [BorelSpace K]
def integersCompact : TopologicalSpace.PositiveCompacts K :=
  ⟨⟨𝒪[K], IsNonarchimedeanLocalField.isCompact_closedBall K 1⟩,
    by
      rw [(valuation K).isOpen_integer.interior_eq]
      exact ⟨0, by simp⟩⟩
def additiveHaar : MeasureTheory.Measure K :=
  MeasureTheory.Measure.addHaarMeasure (integersCompact K)
instance additiveHaar_isAddHaarMeasure : (additiveHaar K).IsAddHaarMeasure := by
  unfold additiveHaar
  infer_instance
theorem additiveHaar_integers : additiveHaar K (𝒪[K] : Set K) = 1 :=
  MeasureTheory.Measure.addHaarMeasure_self
def residueCardinality : ℕ := Nat.card 𝓀[K]
omit [MeasurableSpace K] [BorelSpace K] in
theorem residueCardinality_pos : 0 < residueCardinality K := Nat.card_pos
theorem integers_measurableEmbedding :
    MeasurableEmbedding (fun x : 𝒪[K] => (x : K)) :=
  MeasurableEmbedding.subtype_coe (valuation K).isOpen_integer.measurableSet
def integersHaar : MeasureTheory.Measure 𝒪[K] :=
  (additiveHaar K).comap (fun x : 𝒪[K] => (x : K))
instance integersHaar_isAddLeftInvariant : (integersHaar K).IsAddLeftInvariant :=
  MeasureTheory.Measure.IsAddLeftInvariant.comap (additiveHaar K)
    (f := (𝒪[K]).subtype.toAddMonoidHom) (integers_measurableEmbedding K)
theorem integersHaar_apply (s : Set 𝒪[K]) :
    integersHaar K s = additiveHaar K ((fun x : 𝒪[K] => (x : K)) '' s) :=
  (integers_measurableEmbedding K).comap_apply (additiveHaar K) s
theorem integersHaar_univ : integersHaar K Set.univ = 1 := by
  rw [integersHaar_apply]
  simpa using additiveHaar_integers K
instance integersHaar_isProbabilityMeasure : IsProbabilityMeasure (integersHaar K) :=
  ⟨integersHaar_univ K⟩
omit [MeasurableSpace K] [BorelSpace K] in
theorem maximalIdeal_ne_bot : 𝓂[K] ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field 𝒪[K]
omit [MeasurableSpace K] [BorelSpace K] in
/-- The finite additive index of the nth maximal-ideal power is q^n. -/
theorem maximalIdeal_pow_index (n : ℕ) :
    (𝓂[K] ^ n).toAddSubgroup.index = residueCardinality K ^ n := by
  exact cardQuot_pow_of_prime (maximalIdeal_ne_bot K)
instance maximalIdeal_pow_finiteIndex (n : ℕ) : (𝓂[K] ^ n).toAddSubgroup.FiniteIndex :=
  ⟨by rw [maximalIdeal_pow_index]; exact pow_ne_zero n (residueCardinality_pos K).ne'⟩
def integralUnits : Set 𝒪[K] := (𝓂[K] : Set 𝒪[K])ᶜ
def integralShell (n : ℕ) : Set 𝒪[K] :=
  ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) \ ((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Set 𝒪[K])
def collisionTail (n : ℕ) : Set 𝒪[K] :=
  (fun x : 𝒪[K] => x - 1) ⁻¹' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
def unitConditionalMass (s : Set 𝒪[K]) : ℝ :=
  (integersHaar K).real (s ∩ integralUnits K) /
    (integersHaar K).real (integralUnits K)
def unitCenteredTail (a : 𝒪[K]ˣ) (n : ℕ) : Set 𝒪[K] :=
  (fun x : 𝒪[K] => x - (a : 𝒪[K])) ⁻¹'
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
instance additiveHaar_nullSingletonClass : NullSingletonClass (additiveHaar K) :=
  localField_haar_nullSingletonClass K (additiveHaar K)
end FourierJacobi.Measure


