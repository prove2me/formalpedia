-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueBounds
-- name    : liuyao_ca_fd889115_k1_Analysis_RealValueBounds
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:56:45.736215+00:00
-- url     : https://prove2.me/theorems/4491ae6d-a5ba-404f-b1f9-299ae612cae9
-- title:
--   Computable analysis · RealValueBounds · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RealValueBounds.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealApproximationOrder
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealIntervalImage

set_option autoImplicit true

/-! Arithmetic of exact real error bounds. Rational samples are used only
to prove finite algebra; all values remain their represented computations. -/
namespace ComputableAnalysis.RealApproximationOrder
open ComputableCoefficient RawLimit
set_option maxHeartbeats 1500000

theorem Small.congr {x y : Value} {B : Rat} (h : Small x B)
    (he : x.real.preferred.Equiv y.real.preferred) : Small y B :=
  inInterval_congr (I := {lo := -B,hi := B}) x.real.valid y.real.valid he h

theorem Small.mono {x : Value} {B C : Rat} (h : Small x B) (hBC : B≤C) : Small x C := by
  apply RealIntervalImage.weaken (I := {lo := -B,hi := B}) (J := {lo := -C,hi := C}) h
  change -C≤ -B ∧ B≤C
  exact ⟨Rat.neg_le_neg hBC,hBC⟩

theorem Small.neg {x : Value} {B : Rat} (h : Small x B) : Small (Value.neg x) B := by
  have hn := RealIntervalImage.neg (I := {lo := -B,hi := B}) h
  change InInterval (-x.real.preferred) {lo := -B,hi := B}
  simpa only [Rat.neg_neg] using hn

theorem Small.add {x y : Value} {B C : Rat} (hx : Small x B) (hy : Small y C) :
    Small (Value.add x y) (B+C) := by
  have h := RealIntervalImage.add (I := {lo := -B,hi := B}) (J := {lo := -C,hi := C}) x.real.valid y.real.valid hx hy
  constructor
  · intro i j
    have hh := h.1 i j
    change -B+ -C≤((x.real.preferred+y.real.preferred).compute j).hi at hh
    change -(B+C)≤((x.real.preferred+y.real.preferred).compute j).hi
    grind only
  · intro i j; exact h.2 i j

theorem Small.scale_nonnegative {x : Value} {B c : Rat} (hc : 0≤c) (h : Small x B) :
    Small (scale c x) (c*B) := by
  constructor
  · intro i j
    have hh := Rat.mul_le_mul_of_nonneg_left (h.1 0 j) hc
    change c*(-B)≤c*(x.real.preferred.compute j).hi at hh
    change -(c*B)≤(RealCompute.scaleRatCompute c x.real.preferred j).hi
    simp only [RealCompute.scaleRatCompute,if_pos hc]
    grind only
  · intro i j
    have hh := Rat.mul_le_mul_of_nonneg_left (h.2 i 0) hc
    change c*(x.real.preferred.compute i).lo≤c*B at hh
    change (RealCompute.scaleRatCompute c x.real.preferred i).lo≤c*B
    simpa only [RealCompute.scaleRatCompute,if_pos hc] using hh

theorem Small.mul {x y : Value} {B C : Rat} (hx : Small x B) (hy : Small y C) :
    Small (Value.mul x y) (B*C) := by
  have points (n : Nat) : ∃ p, -(B*C)≤p ∧ p≤B*C ∧
      ((Value.mul x y).real.compute n).lo≤p ∧ p≤((Value.mul x y).real.compute n).hi := by
    obtain ⟨a,haL,haR,ha,ha'⟩ := RealIntervalImage.common_point (I := {lo := -B,hi := B}) x.real.valid hx n
    obtain ⟨b,hbL,hbR,hb,hb'⟩ := RealIntervalImage.common_point (I := {lo := -C,hi := C}) y.real.valid hy n
    have habsA := qabs_le_of_neg_le_le haL haR
    have habsB := qabs_le_of_neg_le_le hbL hbR
    have habs := rat_mul_le_mul_of_nonneg (qabs_nonneg a) habsA (qabs_nonneg b) habsB
    rw [←qabs_mul] at habs
    have hl := neg_qabs_le_self (a*b)
    have hr := self_le_qabs (a*b)
    have hp := QBox.mulRealInterval_contains ha ha' hb hb'
    exact ⟨a*b,by grind only,by grind only,hp.1,hp.2⟩
  constructor
  · intro i j
    obtain ⟨p,hp,_,_,hp'⟩ := points j
    exact Rat.le_trans hp hp'
  · intro i j
    obtain ⟨p,_,hp,hp',_⟩ := points i
    exact Rat.le_trans hp' hp

theorem arithmetic_identity (x y : Value)
    (h : ∀ s : RealCompute.Certified → Rat, x.sample s=y.sample s) : x.real.preferred.Equiv y.real.preferred := by
  apply Value.equiv_of_samples x y 0
  intro _ _ s _
  exact h s

end ComputableAnalysis.RealApproximationOrder


