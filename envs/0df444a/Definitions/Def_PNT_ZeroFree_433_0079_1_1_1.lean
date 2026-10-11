-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0079_1_1_1
-- name    : PNT_ZeroFree_433_0079_1_1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T21:55:19.456149+00:00
-- url     : https://prove2.me/theorems/ef8131c8-1666-4127-aeda-0bd05679c2ca
-- title:
--   Zero-free region foundations: CubicSieve.ChildTransfer [0079_1_1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.ChildTransfer
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ChildTransfer.lean#L154-L167

import Definitions.Def_PNT_ZeroFree_433_0079_1_1_1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ChildTransfer.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace SecondPassArithmetic

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

open scoped BigOperators Classical


section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportConjugateSum)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondInputCoefficient_union (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (G U : Finset ι) (hd : Disjoint G U) :
    secondInputCoefficient p hg Ψ m c d H (G ∪ U) =
      secondInputCoefficient p hg Ψ m c d (fun _ => 1) G *
        secondInputCoefficient p hg Ψ m c d (fun V => H (G ∪ V)) U := by
  simp only [secondInputCoefficient, Finset.prod_union hd, map_mul,
    FirstPassCubeLabels.mask_union _ hg G U hd,
    FirstPassCubeLabels.row_union _ hg G U hd, mul_pow, mul_one]
  ring

def inputConjugateRow (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (z : O) : ℂ :=
  supportConjugateSum (fun i => Ideal.span {p i}) hg F
    (secondInputCoefficient p hg Ψ m c d H) z


end


end


end SecondPassArithmetic

end

end OAI

end


