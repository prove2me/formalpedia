-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_MonotoneLogarithm
-- name    : liuyao_ca_fd889115_k1_Analysis_MonotoneLogarithm
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:01:04.956193+00:00
-- url     : https://prove2.me/theorems/01eeb01f-76e8-49b5-9e8b-ce34da3f9ae8
-- title:
--   Computable analysis · MonotoneLogarithm · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/MonotoneLogarithm.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_DyadicReciprocalIntegral
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralLaws
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueArithmetic

set_option autoImplicit true

/-! The primary positive rational logarithm is oriented dyadic quadrature of
1/x from 1. Its increment and strict-order laws are derived from actual
integrals. Exponential identification is a subsequent obligation. -/
namespace ComputableAnalysis.MonotoneLogarithm
open Integral RealComputeQuotient
open DyadicReciprocalIntegral
set_option maxHeartbeats 1000000

def intervalValue (a b : Rat) (ha : 0<a) (hab : a≤b) : ComputableAnalysis.Real :=
  ofRaw (integral a b ha hab) (valid a b ha hab)

theorem adjacent (a b c : Rat) (ha : 0<a) (hab : a≤b) (hbc : b≤c) :
    (integral a c ha (Rat.le_trans hab hbc)).Equiv
      (RealCompute.add (integral a b ha hab) (integral b c (by grind only) hbc)) := by
  let F := function a c ha
  have hI : HasIntegral (F.restrict a b (Rat.le_refl) hab hbc) (integral a b ha hab) :=
    hasIntegral a b ha hab
  have hJ : HasIntegral (F.restrict b c hab hbc (Rat.le_refl)) (integral b c (by grind only) hbc) :=
    hasIntegral b c (by grind only) hbc
  exact HasIntegral.append_identity (F := F) b hab hbc hI hJ (hasIntegral a c ha (Rat.le_trans hab hbc))

theorem adjacent_value (a b c : Rat) (ha : 0<a) (hab : a≤b) (hbc : b≤c) :
    intervalValue a c ha (Rat.le_trans hab hbc)=
      intervalValue a b ha hab+intervalValue b c (by grind only) hbc :=
  ofRaw_eq_ofRaw (adjacent a b c ha hab hbc)

def sample (q : Rat) (hq : 0<q) : RealCompute :=
  if h : 1≤q then integral 1 q (by decide +kernel) h
  else -(integral q 1 hq (by grind only))

theorem sample_valid (q : Rat) (hq : 0<q) : (sample q hq).Valid := by
  unfold sample
  split
  · exact valid _ _ _ _
  · exact RealCompute.neg_valid (valid _ _ _ _)

def sampleValue (q : Rat) (hq : 0<q) : ComputableAnalysis.Real := ofRaw (sample q hq) (sample_valid q hq)

theorem value_of_ge (q : Rat) (hq : 0<q) (h : 1≤q) :
    sampleValue q hq=intervalValue 1 q (by decide +kernel) h := by
  simp only [sampleValue,sample,dif_pos h]
  rfl

theorem value_of_lt (q : Rat) (hq : 0<q) (h : ¬1≤q) :
    sampleValue q hq= -intervalValue q 1 hq (by grind only) := by
  simp only [sampleValue,sample,dif_neg h]
  rfl

/-- Every rational increment is the independently constructed integral over
that whole positive segment, including segments crossing the base point 1. -/
theorem increment (p q : Rat) (hp : 0<p) (hpq : p≤q) :
    sampleValue q (by grind only)=sampleValue p hp+intervalValue p q hp hpq := by
  have hq : 0<q := by grind only
  by_cases hp1 : 1≤p
  · have hq1 : 1≤q := Rat.le_trans hp1 hpq
    rw [value_of_ge p hp hp1,value_of_ge q hq hq1]
    exact adjacent_value 1 p q (by decide +kernel) hp1 hpq
  · by_cases hq1 : 1≤q
    · rw [value_of_lt p hp hp1,value_of_ge q hq hq1]
      have hi := adjacent_value p 1 q hp (by grind only) hq1
      grind
    · rw [value_of_lt p hp hp1,value_of_lt q hq hq1]
      have hi := adjacent_value p q 1 hp hpq (by grind only)
      grind

/-- Quantitative increment bounds. The integrand's monotonicity supplies the
bounds; interval additivity supplies the increment identity. -/
theorem increment_bounds (p q : Rat) (hp : 0<p) (hpq : p≤q) :
    ofRat ((q-p)/q)≤sampleValue q (by grind only)-sampleValue p hp ∧
      sampleValue q (by grind only)-sampleValue p hp≤ofRat ((q-p)/p) := by
  have hi := increment p q hp hpq
  have hv := value_bounds p q hp hpq
  have hl : ofRat ((q-p)/q)≤intervalValue p q hp hpq := hv.1
  have hu : intervalValue p q hp hpq≤ofRat ((q-p)/p) := hv.2
  have he : sampleValue q (by grind only)-sampleValue p hp=intervalValue p q hp hpq := by grind
  rw [he]
  exact ⟨hl,hu⟩

theorem monotone (p q : Rat) (hp : 0<p) (hpq : p≤q) :
    (sample p hp).Le (sample q (by grind only)) := by
  have hb := (increment_bounds p q hp hpq).1
  have hr : (0 : Rat)≤(q-p)/q := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by grind only) (Rat.le_of_lt (Rat.inv_pos.mpr (by grind only)))
  have hz : (0 : ComputableAnalysis.Real)≤ofRat ((q-p)/q) := fun _ _ => hr
  exact (sub_nonneg_iff _ _).mp (le_trans hz hb)

/-- Strict order is witnessed by a decidable finite separation of the actual
primary sample boxes, rather than a comparison oracle for real values. -/
theorem strictly_increasing (p q : Rat) (hp : 0<p) (hpq : p<q) :
    ∃ n,((sample p hp).compute n).hi<((sample q (by grind only)).compute n).lo := by
  have hq : 0<q := by grind only
  let c := (q-p)/q
  have hc : 0<c := by
    dsimp [c]
    rw [Rat.div_def]
    exact Rat.mul_pos (by grind only) (Rat.inv_pos.mpr hq)
  have hb := (increment_bounds p q hp (Rat.le_of_lt hpq)).1
  have horder : sampleValue p hp+ofRat c≤sampleValue q hq := by
    have h := add_le_add hb (le_refl (sampleValue p hp))
    have he : sampleValue q hq-sampleValue p hp+sampleValue p hp=sampleValue q hq := by grind
    have he' : ofRat c+sampleValue p hp=sampleValue p hp+ofRat c := add_comm _ _
    rw [he',he] at h
    exact h
  let eps : QPos := ⟨c/4,by rw [Rat.div_def]; exact Rat.mul_pos hc (Rat.inv_pos.mpr (by decide +kernel))⟩
  obtain ⟨N,hN⟩ := (sample_valid p hp).2.2 eps
  obtain ⟨M,hM⟩ := (sample_valid q hq).2.2 eps
  let k := max N M
  refine ⟨k,?_⟩
  have hw1 := hN k (Nat.le_max_left _ _)
  have hw2 := hM k (Nat.le_max_right _ _)
  have ho := horder k k
  change ((sample p hp).compute k).lo+c≤((sample q hq).compute k).hi at ho
  dsimp [eps,QInterval.width] at hw1 hw2
  grind only

def raw : PartialRealFunRaw where
  definedAt := fun q => 0<q
  compute q hq := (sample q hq).compute

theorem raw_valid : raw.Valid := sample_valid

theorem at_one : (sample 1 (by decide +kernel)).Equiv (RealCompute.ofRat 0) := by
  have hb := value_bounds 1 1 (by decide +kernel) (Rat.le_refl)
  have he : ((1 : Rat)-1)/1=0 := by decide +kernel
  rw [he] at hb
  apply RealCompute.le_antisymm
  · exact hb.2
  · exact hb.1

end ComputableAnalysis.MonotoneLogarithm


