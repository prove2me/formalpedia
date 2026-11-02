-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FellerCoordinatePolynomialContinuity
-- name    : MarkovProcess_V3HRepair_FellerCoordinatePolynomialContinuity
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:47:24.563451+00:00
-- url     : https://prove2.me/theorems/f02fbe4b-231a-4dce-809c-c07ce9038ac7
-- title:
--   Verified MarkovProcess source repair: FellerCoordinatePolynomialContinuity
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess FellerCoordinatePolynomialContinuity module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.FellerCoordinatePolynomialContinuity source SHA-256 40c162feed71665b282b2897a9efd6f6296ff53b75f51b7bc52c2743885cc92e. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. V6 import variant uses the V3H-local source-derived time-continuity repair and the published backward-recursion integral identity.

import Definitions.Def_MarkovProcess_V3H_Feller_BackwardC0Integral_1512e54f
import Definitions.Def_MarkovProcess_V3H_FiniteTime_CoordinateProductActiveReduction_0fcd6a29
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_MarkovProcess_V3HRepair_FellerCoordinateProductContinuityV6

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported
namespace MarkovProcess.SubMarkovKernelSemigroup
variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem integrable_coordinateProductTerm
    {n : ℕ} (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha)
    (mu : Measure (Fin n → alpha)) [IsFiniteMeasure mu] :
    Integrable term.toContinuousMap mu := by
  have hprod : StronglyMeasurable (fun path : Fin n → alpha ↦
      (term.factors.map fun p ↦ p.2 (path p.1)).prod) := by
    induction term.factors with
    | nil => exact stronglyMeasurable_const
    | cons p factors ih =>
        simp only [List.map_cons, List.prod_cons]
        exact ((p.2.measurable.comp (measurable_pi_apply p.1)).stronglyMeasurable).mul ih
  have hfun : (term.toContinuousMap : (Fin n → alpha) → ℝ) = fun path ↦
      term.coefficient * (term.factors.map fun p ↦ p.2 (path p.1)).prod := by
    funext path
    exact PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply term path
  rw [hfun]
  refine Integrable.of_bound (hprod.const_mul term.coefficient).aestronglyMeasurable
    (‖term.coefficient‖ * (term.factors.map fun p ↦ ‖p.2‖).prod) ?_
  filter_upwards [] with path
  rw [norm_mul, List.norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  induction term.factors with
  | nil =>
      simp only [List.map_nil, List.prod_nil]
      exact le_rfl
  | cons p factors ih =>
      simp only [List.map_cons, List.prod_cons]
      have all_nonneg : ∀ fs : List (Fin n × C₀(alpha, ℝ)),
          0 ≤ (fs.map fun q ↦ ‖q.2 (path q.1)‖).prod := by
        intro fs
        induction fs with
        | nil => simp only [List.map_nil, List.prod_nil, zero_le_one]
        | cons q fs ih_nonneg =>
            simp only [List.map_cons, List.prod_cons]
            exact mul_nonneg (norm_nonneg _) ih_nonneg
      have hnonneg : 0 ≤
          ((factors.map fun p ↦ p.2 (path p.1)).map norm).prod := by
        simpa only [List.map_map, Function.comp_apply] using! all_nonneg factors
      exact mul_le_mul (p.2.toBCF.norm_coe_le_norm (path p.1)) ih
        hnonneg (norm_nonneg _)

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem integrable_coordinatePolynomial
    {n : ℕ} (terms : List (PiContinuousMap.CoordinateProductTerm (Fin n) alpha))
    (mu : Measure (Fin n → alpha)) [IsFiniteMeasure mu] :
    Integrable (PiContinuousMap.coordinatePolynomial terms) mu := by
  induction terms with
  | nil =>
      simp only [PiContinuousMap.coordinatePolynomial_nil]
      change Integrable (fun _ : Fin n → alpha ↦ (0 : ℝ)) mu
      refine Integrable.of_bound stronglyMeasurable_const.aestronglyMeasurable 0 ?_
      exact ae_of_all _ fun _ ↦ by
        simpa only [norm_zero] using (le_refl (0 : ℝ))
  | cons term terms ih =>
      rw [PiContinuousMap.coordinatePolynomial_cons]
      exact (integrable_coordinateProductTerm term mu).add ih

/-- Finite-time integrals of an explicit coordinate polynomial vary continuously under
coordinatewise convergence of the ordered observation times. -/
theorem IsFellerKernelSemigroup.tendsto_integral_coordinatePolynomial_finiteTimeKernel
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes n} {times0 : FiniteOrderedTimes n}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times0 i)))
    (terms : List (PiContinuousMap.CoordinateProductTerm (Fin n) alpha)) (x : alpha) :
    Tendsto (fun a ↦ ∫ path, PiContinuousMap.coordinatePolynomial terms path
        ∂finiteTimeKernel P (times a) x) l
      (nhds (∫ path, PiContinuousMap.coordinatePolynomial terms path
        ∂finiteTimeKernel P times0 x)) := by
  induction terms with
  | nil =>
      simp only [PiContinuousMap.coordinatePolynomial_nil, ContinuousMap.zero_apply,
        integral_zero]
      exact tendsto_const_nhds
  | cons term terms ih =>
      have hIntegral (u : FiniteOrderedTimes n) :
          ∫ path, PiContinuousMap.coordinatePolynomial (term :: terms) path
              ∂finiteTimeKernel P u x =
            (∫ path, term.toContinuousMap path ∂finiteTimeKernel P u x) +
              ∫ path, PiContinuousMap.coordinatePolynomial terms path
                ∂finiteTimeKernel P u x := by
        let : IsProbabilityMeasure (finiteTimeKernel P u x) :=
          hP.isProbabilityMeasure_finiteTimeLaw P u x
        rw [PiContinuousMap.coordinatePolynomial_cons]
        apply integral_add
        · exact integrable_coordinateProductTerm term _
        · exact integrable_coordinatePolynomial terms _
      simp_rw [hIntegral]
      exact (hFeller.tendsto_integral_coordinateProductTerm_finiteTimeKernel
        hP ht term x).add ih


end MarkovProcess.SubMarkovKernelSemigroup


