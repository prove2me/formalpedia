-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0153_1
-- name    : PNT_ZeroFree_433_0153_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:19:33.000832+00:00
-- url     : https://prove2.me/theorems/c36d7d5f-1261-4c2d-a1de-304b00aa6a3e
-- title:
--   Zero-free region foundations: CubicSieve.NormalizedMass [0153_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.NormalizedMass
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/NormalizedMass.lean#L199-L275

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0059
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0133
import Definitions.Def_PNT_ZeroFree_433_0141_parallel1
import Definitions.Def_PNT_ZeroFree_433_0142
import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0153_parallel1
import Definitions.Def_PNT_ZeroFree_433_0153_parallel2
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/NormalizedMass.lean
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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic


section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

def globalFirstColumnMass (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) : ℝ :=
  ∑G∈(globalFirstRawPool pool b).powerset,
    ‖secondInputCoefficient p hg Ψ (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) G‖^2

include hp in
theorem globalFirstColumnMass_support (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ,ℂ)) (ell M : ℝ) (hell : 0<ell)
    (hM : ∀t,g t≠0 → |t|≤M) (side : Bool)
    (hmass : globalFirstColumnMass p hg pool b Ψ m g ell side≠0) :
    primeProductNorm p b.common≤ell*Real.exp M ∧
      primeProductNorm p b.firstCommon≤ell*Real.exp M := by
  let a := primeProductNorm p (b.cube.sideDivisor side)
  let c := primeProductNorm p b.common
  let t := primeProductNorm p b.firstCommon
  have ha : 1≤a := primeProductNorm_ge_one p hp _
  have hc : 1≤c := primeProductNorm_ge_one p hp _
  have ht : 1≤t := primeProductNorm_ge_one p hp _
  have hden : 0<a*c*t := by positivity
  have hX : 0<globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon := by
    change 0<ell/(a*c)/t
    positivity
  have hlow : 1≤(globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon)*Real.exp M := by
    by_contra hh
    apply hmass
    exact normalized_second_mass_zero p hp hg (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) g M
      (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon) hX hM (lt_of_not_ge hh)
  have heq : (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon)*Real.exp M=
      ell*Real.exp M/(a*c*t) := by change (ell/(a*c)/t)*Real.exp M=_; ring
  rw [heq] at hlow
  have hb : a*c*t≤ell*Real.exp M := by simpa only [one_mul] using (le_div_iff₀ hden).mp hlow
  constructor
  · change c≤_
    calc
      c=1*c*1 := by ring
      _ ≤ a*c*t := by gcongr
      _ ≤ _ := hb
  · change t≤_
    calc
      t=1*1*t := by ring
      _ ≤ a*c*t := by gcongr
      _ ≤ _ := hb

include hp in
theorem globalFirstColumnMass_zero_off_support (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ,ℂ)) (ell M U : ℝ) (hell : 0<ell)
    (hM : ∀t,g t≠0 → |t|≤M) (hU : ell*Real.exp M≤U) (side : Bool)
    (hoff : ¬(primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)) :
    globalFirstColumnMass p hg pool b Ψ m g ell side=0 := by
  by_contra hm
  have h := globalFirstColumnMass_support p hp hg pool b Ψ m g ell M hell hM side hm
  exact hoff ⟨h.1.trans hU,h.2.trans hU⟩

include hp in
theorem globalFirstDiagonalCost_eq_supported (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (ell M U : ℝ) (hell : 0<ell) (hM : ∀t,g t≠0 → |t|≤M)
    (hU : ell*Real.exp M≤U) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstDiagonalCost p hg pool s w Ψ m g W ell side Y=
      globalFirstDiagonalCost p hg pool
        (s.filter (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U))
        w Ψ m g W ell side Y := by
  unfold globalFirstDiagonalCost
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro b hb hn
  have hoff : ¬(primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U) := by
    intro h; exact hn (Finset.mem_filter.mpr ⟨hb,h⟩)
  have hz := globalFirstColumnMass_zero_off_support p hp hg pool b Ψ m g ell M U hell hM hU side hoff
  change globalFirstColumnMass p hg pool b Ψ m g ell side=0 at hz
  change ‖w b‖*(primeProductNorm p b.firstCommon)⁻¹*
    (|Y b| *‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖*globalFirstColumnMass p hg pool b Ψ m g ell side)=0
  rw [hz,mul_zero,mul_zero]

end


end SecondPassArithmetic


end

end OAI

end


