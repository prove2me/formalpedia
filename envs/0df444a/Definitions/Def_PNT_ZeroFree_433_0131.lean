-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0131
-- name    : PNT_ZeroFree_433_0131
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:27:07.693024+00:00
-- url     : https://prove2.me/theorems/22deb2aa-fdf1-41b6-9712-8a137b322ae2
-- title:
--   Zero-free region foundations: Eisenstein.HyperbolicVolume [0131]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicVolume
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/HyperbolicVolume.lean#L79-L626

import Definitions.Def_PNT_ZeroFree_433_0130
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/HyperbolicVolume.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
attribute [simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

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


open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups


open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)


theorem globalBin_complete_cost (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) (ray : SecondRayIndex) :
    globalBinFirstCoefficient K ell B F j *
      globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *
      (globalPooledColumnScale ell j*globalPooledLabelScale j) *
      (128^3*(Real.exp 1)^3*globalBinTripleRange B j) =
    globalBinChildCharge B F j*‖secondRayCoefficient ray‖ := by
  have h (i : Fin 10) := (globalLogRep_pos j i).ne'
  have hs := (Real.sqrt_pos.mpr (globalLogRep_pos j 9)).ne'
  have he : Real.exp 4=(Real.exp 1)^4 := by simp
  unfold globalBinFirstCoefficient globalPooledOuterBound globalPooledRowScale
    globalPooledColumnScale globalPooledLabelScale globalBinTripleRange globalBinChildCharge globalPooledDelta
  rw [he]
  field_simp [h]

theorem globalBin_mass_balance (ell B F : ℝ) (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) :
    globalBinChildCharge B F j*(globalPooledColumnScale ell j*globalPooledLabelScale j) =
      128^3*(Real.exp 1)^18*((ell*B^3)*F) := by
  rw [globalPooled_mass ell B F hB hF]
  have hD := (globalPooledDelta_pos B F hB hF j).ne'
  have hJ := (globalLogRep_pos j 4).ne'
  have he : Real.exp 4=(Real.exp 1)^4 := by simp
  unfold globalBinChildCharge
  rw [he]
  field_simp

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalBin_active_bounds (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    Real.sqrt (globalLogRep (globalScaleIndex p side x) 9) ≤ globalCubeActiveRoot p x ∧
    globalCubeActiveRoot p x ≤ Real.sqrt (globalLogRep (globalScaleIndex p side x) 9)*Real.exp 1 := by
  have hr := globalScaleIndex_bounds p hp side x hk 9
  change globalLogRep (globalScaleIndex p side x) 9 ≤ (globalCubeActiveRoot p x)^2 ∧
    (globalCubeActiveRoot p x)^2 ≤ globalLogRep (globalScaleIndex p side x) 9*Real.exp 1 at hr
  have hx := (globalCubeActiveRoot_pos p hp x).le
  constructor
  · exact Real.sqrt_le_iff.mpr ⟨hx,hr.1⟩
  · have hs := Real.sq_sqrt (globalLogRep_pos (globalScaleIndex p side x) 9).le
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hrep := (globalLogRep_pos (globalScaleIndex p side x) 9).le
    have hm : (globalCubeActiveRoot p x)^2 ≤
        (Real.sqrt (globalLogRep (globalScaleIndex p side x) 9)*Real.exp 1)^2 := by
      calc
        _ ≤ globalLogRep (globalScaleIndex p side x) 9*Real.exp 1 := hr.2
        _ ≤ globalLogRep (globalScaleIndex p side x) 9*(Real.exp 1)^2 := by gcongr; nlinarith
        _ = _ := by rw [mul_pow,hs]
    exact (sq_le_sq₀ hx (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos 1).le)).mp hm

include hp in
theorem globalBin_first_coefficient_bound (K ell B F : ℝ) (hK : 0 ≤ K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0) :
    K/(primeProductNorm p x.firstDivisor*ell*B^2*F*globalCubeActiveRoot p x) ≤
      globalBinFirstCoefficient K ell B F (globalScaleIndex p side x) := by
  have hd := (globalScaleIndex_bounds p hp side x hk 5).1
  have ha := (globalBin_active_bounds p hp side x hk).1
  change globalLogRep (globalScaleIndex p side x) 5 ≤ primeProductNorm p x.firstDivisor at hd
  have h5 := globalLogRep_pos (globalScaleIndex p side x) 5
  have hs := Real.sqrt_pos.mpr (globalLogRep_pos (globalScaleIndex p side x) 9)
  have hd0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstDivisor).le
  unfold globalBinFirstCoefficient
  apply div_le_div_of_nonneg_left hK (by positivity)
  gcongr

include hp in
theorem globalBin_triple_bounds (B : ℝ) (hB : 0 < B) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    let j := globalScaleIndex p side x
    (Ideal.absNorm (globalSecondFixedTriple p x).1 : ℝ) ≤ B*(Real.sqrt (globalLogRep j 9)*Real.exp 1)/globalLogRep j 4 ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.1 : ℝ) ≤ globalLogRep j 2*Real.exp 1 ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.2 : ℝ) ≤ globalLogRep j 3*Real.exp 1 := by
  dsimp only
  exact globalSecondFixedTriple_norm_bounds p hp x B _ _ _ _ hB.le (globalLogRep_pos _ 4)
    hb₁ hb₂ (globalBin_active_bounds p hp side x hk).2
    (globalScaleIndex_bounds p hp side x hk 4).1
    (globalScaleIndex_bounds p hp side x hk 2).2 (globalScaleIndex_bounds p hp side x hk 3).2

include hp in

theorem globalBin_triple_count (B : ℝ) (hB : 0 < B) (side : Bool)
    (s : Finset (GlobalSecondData ι)) (j : GlobalLogIndex)
    (hj : ∀ x∈s,globalScaleIndex p side x=j)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    ((s.image (globalSecondFixedTriple p)).card : ℝ) ≤
      128^3*(Real.exp 1)^3*globalBinTripleRange B j := by
  by_cases hs : s.Nonempty
  · obtain ⟨x,hxs⟩ := hs
    have hb := globalBin_triple_bounds p hp B hB side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)
    dsimp only at hb
    rw [hj x hxs] at hb
    have hn : 1 ≤ (Ideal.absNorm (globalSecondFixedTriple p x).1 : ℝ) := by
      have hh : 1 ≤ Ideal.absNorm (globalSecondFixedTriple p x).1 :=
        Nat.one_le_iff_ne_zero.mpr (fun h => (globalSecondFixedTriple_nonzero p hp x).1 (Ideal.absNorm_eq_zero_iff.mp h))
      exact_mod_cast hh
    have hcount := globalSecondFixedTriple_count p hp s B
      (Real.sqrt (globalLogRep j 9)*Real.exp 1) (globalLogRep j 4)
      (globalLogRep j 2*Real.exp 1) (globalLogRep j 3*Real.exp 1)
      hB.le (globalLogRep_pos j 4) (hn.trans hb.1)
      (one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 2) (Real.one_le_exp (by norm_num)))
      (one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 3) (Real.one_le_exp (by norm_num))) hb₁ hb₂
      (fun y hy => by have hh := (globalBin_active_bounds p hp side y (hk y hy)).2; rwa [hj y hy] at hh)
      (fun y hy => by have hh := (globalScaleIndex_bounds p hp side y (hk y hy) 4).1; rwa [hj y hy] at hh)
      (fun y hy => by have hh := (globalScaleIndex_bounds p hp side y (hk y hy) 2).2; rwa [hj y hy] at hh)
      (fun y hy => by have hh := (globalScaleIndex_bounds p hp side y (hk y hy) 3).2; rwa [hj y hy] at hh)
    convert! hcount using 1 ; unfold globalBinTripleRange ; ring
  · have hz : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hz]
    simp only [Finset.image_empty,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (by positivity) (globalBinTripleRange_nonneg B hB.le j)

end SecondPassArithmetic

end

end OAI

end


