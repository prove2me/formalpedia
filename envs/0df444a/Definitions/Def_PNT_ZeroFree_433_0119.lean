-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0119
-- name    : PNT_ZeroFree_433_0119
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:43:23.684508+00:00
-- url     : https://prove2.me/theorems/aac010e3-3fa3-4392-b437-103f37a43e08
-- title:
--   Zero-free region foundations: CubicSieve.GlobalEncoding [0119]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.GlobalEncoding
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/GlobalEncoding.lean#L82-L669

import Definitions.Def_PNT_ZeroFree_433_0113
import Definitions.Def_PNT_ZeroFree_433_0118
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/GlobalEncoding.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
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
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical


open scoped BigOperators Classical SchwartzMap


open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel b0Label jLabel cubeActiveSupport primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)


variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]


omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondFixedTriple_norm_bounds (hp : ∀ i,p i ≠ 0)
    (x : GlobalSecondData ι) (B H J T R : ℝ) (hB : 0 ≤ B) (hJ : 0 < J)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hactive : ‖eisEmbedding (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤ H)
    (hlabel : J ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2)
    (ht : primeProductNorm p x.firstCommon ≤ T)
    (hr : primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ R) :
    (Ideal.absNorm (globalSecondFixedTriple p x).1 : ℝ) ≤ B*H/J ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.1 : ℝ) ≤ T ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.2 : ℝ) ≤ R := by
  obtain ⟨_,_,hb0⟩ := cube_label_norm_bounds p hp x.cube.support
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.cube.support_pos B hB hb₁ hb₂
  refine ⟨?_,?_,?_⟩
  · change (Ideal.absNorm (Ideal.span {_}) : ℝ) ≤ _
    rw [← eisEmbedding_norm_sq_eq_absNorm_span]
    apply hb0.trans
    exact div_le_div₀ (mul_nonneg hB ((norm_nonneg _).trans hactive))
      (mul_le_mul_of_nonneg_left hactive hB) hJ hlabel
  · exact (primeProductNorm_eq_ideal_norm p _).symm ▸ ht
  · exact (primeProductNorm_eq_ideal_norm p _).symm ▸ hr

theorem globalSecondFixedTriple_count (hp : ∀ i,p i ≠ 0)
    (s : Finset (GlobalSecondData ι)) (B H J T R : ℝ)
    (hB : 0 ≤ B) (hJ : 0 < J) (hscale : 1 ≤ B*H/J) (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hb₁ : ∀ x∈s, ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s, ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hactive : ∀ x∈s, ‖eisEmbedding (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤ H)
    (hlabel : ∀ x∈s, J ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2)
    (ht : ∀ x∈s, primeProductNorm p x.firstCommon ≤ T)
    (hr : ∀ x∈s, primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ R) :
    ((s.image (globalSecondFixedTriple p)).card : ℝ) ≤ 128^3*(B*H/J)*T*R := by
  apply DescentFiberCost.fixed_triple_count _ _ _ _ hscale hT hR
  · intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact globalSecondFixedTriple_nonzero p hp x
  · intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact globalSecondFixedTriple_norm_bounds p hp x B H J T R hB hJ
      (hb₁ x hx) (hb₂ x hx) (hactive x hx) (hlabel x hx) (ht x hx) (hr x hx)


end


end SecondPassArithmetic

end

end OAI

end


