-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0127
-- name    : PNT_ZeroFree_433_0127
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:15:29.278661+00:00
-- url     : https://prove2.me/theorems/00aa3b36-4ee1-4d82-9341-eb5106b7d8c7
-- title:
--   Zero-free region foundations: QuadraticSieve.CommonMasks [0127]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.CommonMasks
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CommonMasks.lean#L447-L486

import Definitions.Def_PNT_ZeroFree_433_0127_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CommonMasks.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

open scoped BigOperators Classical SchwartzMap


open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson


theorem originalHigh_gcd_principal_assembly {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (hdiv : ∀ j, D∣cols j) (hproper : ∀ j, cols j≠D)
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*(∑' lengthScale : Ideal O, originalPairHigh (cols j) (cols k) W M K lengthScale) else 0) =
      (∑ q ∈ idealDivisors (commonMaskIdeal D), (UniqueFactorizationMonoid.moebius q:ℂ)*
        retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
          (fun I : squarefreeIdealRange K => I.val) (fun j => idealQuotient D (cols j))
          (fun j => a j*quadraticRow (idealQuotient D (cols j)) (idealGenerator q)) M (Ideal.absNorm q:ℝ)) +
      maskedDualTailFamily (commonMaskIdeal D) (fun j => idealQuotient D (cols j)) a W M K -
      (6:ℂ)⁻¹ * maskedPrincipalSourceSum (commonMaskIdeal D) (quadraticSquareProfile W)
        (fun B : coprimeSquarefreeRange (commonMaskIdeal D) K => B.val)
        (fun j => idealQuotient D (cols j)) a M := by
  have hsplit :
      (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
        star (a j)*a k*(∑' lengthScale : Ideal O, originalPairHigh (cols j) (cols k) W M K lengthScale) else 0) =
      (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
        star (a j)*a k*originalPairDualKernel D (cols j) (cols k) W M else 0) -
      (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
        star (a j)*a k*(∑' lengthScale : Ideal O, originalPairLow (cols j) (cols k) W M K lengthScale) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hg : gcd (cols j) (cols k)=D
    · rw [if_pos hg,if_pos hg,if_pos hg,
        originalPairHigh_eq_source_sub_low (cols j) (cols k) W M K hM,
        originalPairSource_poisson D (cols j) (cols k) (hcols j) (hcols k) hg (hray j k) W M hM]
      ring
    · simp only [hg,ite_false,sub_self]
  rw [hsplit,originalDual_gcd_aggregate D hD cols hcols hdiv hproper hray a W M hM,
    originalLow_gcd_aggregate D hD cols hcols hdiv a W M K hM,
    maskedDualFamily_retained _ (commonMaskIdeal_squarefree D).ne_zero _ a W M K hM
      (fun j => admissible_idealQuotient (hcols j) (hdiv j))
      (fun j k => columnRay_idealQuotient_eq D (cols j) (cols k) (hcols j) (hcols k)
        (hdiv j) (hdiv k) (hray j k))]

end


end CanonicalQuadraticSieve

end

end OAI

end


