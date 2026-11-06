-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
-- name    : OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:24:27.159908+00:00
-- url     : https://prove2.me/theorems/c6a381e8-643f-4fa4-9aee-6e0178d732d9
-- title:
--   Quadratic Normalization
-- statement:
--   Definitions and structural lemmas for Quadratic Normalization, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
noncomputable def quadraticGammaO (c : O) (hc : c ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  exact (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) /
    (‖eisEmbedding c‖ : ℂ)
end ActualEisensteinCubic
namespace PowerExtraction
end PowerExtraction
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace PowerExtraction
end PowerExtraction
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace GaussianAbelPartition
open ConcreteTraceCRT ConcreteBreveE ActualEisensteinCubic
end GaussianAbelPartition
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace GaussianFiberEquiv
open ActualEisensteinCubic
def fiberMap (c : O) (r : O ⧸ Ideal.span {c})
    (r0 : O) (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (w : O) : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) := by
  refine ⟨r0 + c*w, ?_⟩
  change Ideal.Quotient.mk (Ideal.span {c}) (r0 + c*w) = r
  rw [map_add, map_mul]
  have hc0 : Ideal.Quotient.mk (Ideal.span {c}) c = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton c))
  rw [hc0, zero_mul, add_zero, hr]
theorem fiberMap_injective (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Injective (fiberMap c r r0 hr) := by
  intro u v h
  have hval := congrArg Subtype.val h
  change r0 + c*u = r0 + c*v at hval
  exact mul_left_cancel₀ hc (add_left_cancel hval)
theorem fiberMap_surjective (c : O)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Surjective (fiberMap c r r0 hr) := by
  rintro ⟨z, hz⟩
  have hz' : Ideal.Quotient.mk (Ideal.span {c}) z = r := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
  have hdiff : z-r0 ∈ Ideal.span {c} :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem z r0).mp (hz'.trans hr.symm)
  obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton).mp hdiff
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change r0 + c*w = z
  rw [← hw]
  ring
noncomputable def fiberEquiv (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    O ≃ ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) :=
  Equiv.ofBijective (fiberMap c r r0 hr)
    ⟨fiberMap_injective c hc r r0 hr, fiberMap_surjective c r r0 hr⟩
end GaussianFiberEquiv
namespace RankTwoPoisson
open Real
noncomputable def cg (a : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (-((Real.pi : ℂ) * a) * (n : ℂ) ^ 2)
noncomputable def eisQ (z : ℤ × ℤ) : ℝ :=
  (z.1 : ℝ) ^ 2 - (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2
noncomputable def eisGauss (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp ((-Real.pi * t * eisQ z : ℝ) : ℂ)
noncomputable def phase (k n : ℤ) : ℂ :=
  Complex.exp (((-Real.pi * (k : ℝ) * (n : ℝ) : ℝ) : ℂ) * Complex.I)
noncomputable def g1 (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  cg ((t⁻¹ : ℝ) : ℂ) z.1 * cg (((3 * t) / 4 : ℝ) : ℂ) z.2 * phase z.1 z.2
noncomputable def dualTerm (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  cg ((t⁻¹ : ℝ) : ℂ) z.1 *
    Complex.exp (-(Real.pi : ℂ) / (((3 * t) / 4 : ℝ) : ℂ) *
      ((z.2 : ℂ) + (z.1 : ℂ) / 2) ^ 2)
end RankTwoPoisson
end
end OAI


