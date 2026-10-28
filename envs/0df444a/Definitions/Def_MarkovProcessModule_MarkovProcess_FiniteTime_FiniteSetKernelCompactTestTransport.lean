-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_FiniteSetKernelCompactTestTransport
-- name    : MarkovProcessModule_MarkovProcess_FiniteTime_FiniteSetKernelCompactTestTransport
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:05:58.419654+00:00
-- url     : https://prove2.me/theorems/9b9068ac-1b5f-4414-99b1-c5413055b398
-- title:
--   MarkovProcess.FiniteTime.FiniteSetKernelCompactTestTransport
-- statement:
--   # Compact-test transport for finite-set kernels
--
--   This file identifies the increasing-coordinate representation of a finite set with its ordinary
--   function space by a homeomorphism. It transports compactly supported tests across that
--   homeomorphism and rewrites their finite-set-kernel integrals as finite-time-kernel integrals.
--
--   Strong measurability of a compactly supported test is obtained privately from uniform coordinate-
--   polynomial approximations. This avoids adding an `OpensMeasurableSpace` assumption on the finite
--   product. These declarations are finite-dimensional infrastructure; no statement about path space
--   is proved here.
--
--   Complete pinned Lean module MarkovProcess.FiniteTime.FiniteSetKernelCompactTestTransport by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/FiniteSetKernelCompactTestTransport.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_FiniteProductCoordinateNormalForm
import Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_ProjectiveFamily
import Mathlib.MeasureTheory.Integral.CompactlySupported

/-!
# Compact-test transport for finite-set kernels

This file identifies the increasing-coordinate representation of a finite set with its ordinary
function space by a homeomorphism. It transports compactly supported tests across that
homeomorphism and rewrites their finite-set-kernel integrals as finite-time-kernel integrals.

Strong measurability of a compactly supported test is obtained privately from uniform coordinate-
polynomial approximations. This avoids adding an `OpensMeasurableSpace` assumption on the finite
product. These declarations are finite-dimensional infrastructure; no statement about path space
is proved here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup

private theorem stronglyMeasurable_coordinatePolynomial
    {I alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
    (terms : List (PiContinuousMap.CoordinateProductTerm I alpha)) :
    StronglyMeasurable (PiContinuousMap.coordinatePolynomial terms) := by
  induction terms with
  | nil =>
      simp only [PiContinuousMap.coordinatePolynomial_nil]
      exact stronglyMeasurable_const
  | cons term terms ih =>
      rw [PiContinuousMap.coordinatePolynomial_cons]
      apply StronglyMeasurable.add _ ih
      have hprod : StronglyMeasurable (fun path : I → alpha ↦
          (term.factors.map fun p ↦ p.2 (path p.1)).prod) := by
        induction term.factors with
        | nil => exact stronglyMeasurable_const
        | cons p factors ihFactors =>
            simp only [List.map_cons, List.prod_cons]
            exact ((p.2.measurable.comp (measurable_pi_apply p.1)).stronglyMeasurable).mul
              ihFactors
      rw [show (term.toContinuousMap : (I → alpha) → ℝ) = fun path ↦
          term.coefficient * (term.factors.map fun p ↦ p.2 (path p.1)).prod by
        funext path
        exact PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply term path]
      exact hprod.const_mul term.coefficient

private theorem stronglyMeasurable_compactlySupported_pi
    {I alpha : Type*} [Fintype I] [TopologicalSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [T3Space alpha] [LocallyCompactSpace alpha]
    (f : C_c(I → alpha, ℝ)) : StronglyMeasurable f := by
  have hexists (m : ℕ) :
      ∃ terms : List (PiContinuousMap.CoordinateProductTerm I alpha),
        ∀ x, ‖PiContinuousMap.coordinatePolynomial terms x - f x‖ <
          1 / ((m : ℝ) + 1) := by
    have hpositive : 0 < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨terms, hterms⟩ :=
      PiContinuousMap.exists_coordinateProductTerms_near_compactlySupported f hpositive
    exact ⟨terms, fun x ↦ by
      rw [PiContinuousMap.coordinatePolynomial_apply]
      exact hterms x⟩
  choose terms hterms using hexists
  apply stronglyMeasurable_of_tendsto Filter.atTop
    (fun m ↦ stronglyMeasurable_coordinatePolynomial (terms m))
  rw [tendsto_pi_nhds]
  intro x
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hscalar : Filter.Tendsto (fun m : ℕ ↦ (1 : ℝ) / ((m : ℝ) + 1)) Filter.atTop
      (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Metric.tendsto_nhds] at hscalar
  filter_upwards [hscalar epsilon hepsilon] with m hm
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at hm
  exact (hterms m x).trans_le hm.le

/-- The increasing-coordinate representation of paths on a finite time set, as a homeomorphism. -/
noncomputable def orderedPathToFiniteSetHomeomorph
    {alpha : Type*} [TopologicalSpace alpha] (I : Finset NNReal) :
    (Fin I.card → alpha) ≃ₜ (I → alpha) :=
  Homeomorph.piCongrLeft (Y := fun _ : I ↦ alpha) (I.orderIsoOfFin rfl).toEquiv

/-- The ordered-coordinate homeomorphism has underlying function `orderedPathToFiniteSet`. -/
@[simp]
theorem orderedPathToFiniteSetHomeomorph_apply
    {alpha : Type*} [TopologicalSpace alpha] (I : Finset NNReal)
    (path : Fin I.card → alpha) :
    orderedPathToFiniteSetHomeomorph I path = orderedPathToFiniteSet I path := by
  ext t
  change (Equiv.piCongrLeft (fun _ : I ↦ alpha) (I.orderIsoOfFin rfl).toEquiv path) t = _
  rw [Equiv.piCongrLeft_apply]
  simp only [orderedPathToFiniteSet]
  rw [eqRec_eq_cast, cast_eq]
  rfl

/-- Pull a compactly supported test on finite-set coordinates back to increasing coordinates. -/
noncomputable def pullbackFiniteSetCompactTest
    {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
    (I : Finset NNReal) (f : C_c(I → alpha, ℝ)) : C_c(Fin I.card → alpha, ℝ) :=
  f.comp (orderedPathToFiniteSetHomeomorph I).toCocompactMap

/-- Evaluation of a compact test pulled back to increasing coordinates. -/
@[simp]
theorem pullbackFiniteSetCompactTest_apply
    {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
    (I : Finset NNReal) (f : C_c(I → alpha, ℝ)) (path : Fin I.card → alpha) :
    pullbackFiniteSetCompactTest I f path = f (orderedPathToFiniteSet I path) := by
  rw [pullbackFiniteSetCompactTest]
  exact congr_arg f (orderedPathToFiniteSetHomeomorph_apply I path)

/-- Integration against the mapped ordered-coordinate law equals integration of the pulled-back
compact test. -/
theorem integral_map_orderedPathToFiniteSet
    {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
    (I : Finset NNReal) (f : C_c(I → alpha, ℝ))
    (mu : Measure (Fin I.card → alpha)) :
    ∫ y, f y ∂mu.map (orderedPathToFiniteSet I) =
      ∫ path, pullbackFiniteSetCompactTest I f path ∂mu := by
  rw [integral_map (measurable_orderedPathToFiniteSet I).aemeasurable
    (stronglyMeasurable_compactlySupported_pi f).aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun path ↦ (pullbackFiniteSetCompactTest_apply I f path).symm

/-- A compact-test integral against `finiteSetKernel` is the corresponding pulled-back integral
against `finiteTimeKernel`. -/
theorem integral_finiteSetKernel_eq_integral_pullbackFiniteSetCompactTest
    {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
    (P : SubMarkovKernelSemigroup alpha) (I : Finset NNReal)
    (f : C_c(I → alpha, ℝ)) (x : alpha) :
    ∫ y, f y ∂finiteSetKernel P I x =
      ∫ path, pullbackFiniteSetCompactTest I f path
        ∂finiteTimeKernel P (finiteSetTimes I) x := by
  rw [finiteSetKernel_eq_map, Kernel.map_apply _ (measurable_orderedPathToFiniteSet I)]
  exact integral_map_orderedPathToFiniteSet I f (finiteTimeKernel P (finiteSetTimes I) x)

end MarkovProcess.SubMarkovKernelSemigroup


