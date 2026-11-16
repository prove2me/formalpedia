-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealIntervalImage
-- name    : liuyao_ca_fd889115_k1_Analysis_RealIntervalImage
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:54:38.746959+00:00
-- url     : https://prove2.me/theorems/f508be32-210b-4313-98f5-3e6e7b55b06a
-- title:
--   Computable analysis · RealIntervalImage · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RealIntervalImage.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComputableCoefficient
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ParametrizedLimits

set_option autoImplicit true

/-! Semantic real-interval images under arithmetic. A common rational point
in each finite box proves the order bounds without a completed real field. -/
namespace ComputableAnalysis.RealIntervalImage
open RawLimit
set_option maxHeartbeats 1000000

theorem common_point {x : RealCompute} (hx : x.Valid) {I : QInterval}
    (h : InInterval x I) (n : Nat) :
    ∃ q, I.lo≤q ∧ q≤I.hi ∧ (x.compute n).lo≤q ∧ q≤(x.compute n).hi := by
  have hl := h.1 0 n
  have hr := h.2 n 0
  have ho := RealCompute.interval_order_of_valid _ hx n
  have hI : I.lo≤I.hi := RealCompute.le_trans hx h.1 h.2 0 0
  change I.lo≤(x.compute n).hi at hl
  change (x.compute n).lo≤I.hi at hr
  refine ⟨max I.lo (x.compute n).lo,?_,?_,?_,?_⟩ <;> grind

def product (I J : QInterval) : QInterval := QBox.mulRealInterval I.lo I.hi J.lo J.hi

theorem mul {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) {I J : QInterval}
    (hI : InInterval x I) (hJ : InInterval y J) : InInterval (RealCompute.mul x y) (product I J) := by
  have points (n : Nat) : ∃ p,
      (product I J).lo≤p ∧ p≤(product I J).hi ∧
      ((RealCompute.mul x y).compute n).lo≤p ∧ p≤((RealCompute.mul x y).compute n).hi := by
    obtain ⟨a,haI,haI',ha,ha'⟩ := common_point hx hI n
    obtain ⟨b,hbJ,hbJ',hb,hb'⟩ := common_point hy hJ n
    have h1 := QBox.mulRealInterval_contains haI haI' hbJ hbJ'
    have h2 := QBox.mulRealInterval_contains ha ha' hb hb'
    exact ⟨a*b,h1.1,h1.2,h2.1,h2.2⟩
  constructor
  · intro i n
    obtain ⟨p,hp,_,_,hp'⟩ := points n
    exact Rat.le_trans hp hp'
  · intro n i
    obtain ⟨p,_,hp,hp',_⟩ := points n
    exact Rat.le_trans hp' hp

theorem neg {x : RealCompute} {I : QInterval} (h : InInterval x I) :
    InInterval (-x) {lo := -I.hi,hi := -I.lo} := by
  constructor
  · intro i n
    have hh := h.2 n 0
    change (x.compute n).lo≤I.hi at hh
    change -I.hi≤ -(x.compute n).lo
    exact Rat.neg_le_neg hh
  · intro n i
    have hh := h.1 0 n
    change I.lo≤(x.compute n).hi at hh
    change -(x.compute n).hi≤ -I.lo
    exact Rat.neg_le_neg hh

theorem current {x : RealCompute} (hx : x.Valid) (n : Nat) : InInterval x (x.compute n) :=
  ⟨fun _ m => RealCompute.le_refl _ hx n m,fun m _ => RealCompute.le_refl _ hx m n⟩

theorem add {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) {I J : QInterval}
    (hI : InInterval x I) (hJ : InInterval y J) :
    InInterval (x+y) {lo := I.lo+J.lo,hi := I.hi+J.hi} := by
  constructor
  · intro i n
    have h1 := hI.1 0 n
    have h2 := hJ.1 0 n
    change I.lo≤(x.compute n).hi at h1
    change J.lo≤(y.compute n).hi at h2
    change I.lo+J.lo≤(x.compute n).hi+(y.compute n).hi
    exact rat_add_le_add h1 h2
  · intro n i
    have h1 := hI.2 n 0
    have h2 := hJ.2 n 0
    change (x.compute n).lo≤I.hi at h1
    change (y.compute n).lo≤J.hi at h2
    exact rat_add_le_add h1 h2

theorem error_translate {y c : RealCompute} (hy : y.Valid) (hc : c.Valid) {I : QInterval}
    (E : Rat) (hE : InInterval (y-c) {lo := -E,hi := E}) (hI : InInterval c I) :
    InInterval y (QInterval.expand I E) := by
  have hs := add (RealCompute.sub_valid hy hc) hc hE hI
  have hv := RealCompute.add_valid (RealCompute.sub_valid hy hc) hc
  have he := RealCompute.sub_add_cancel_equiv hy hc
  have h := inInterval_congr hv hy he hs
  constructor
  · intro i j
    have hh := h.1 i j
    change -E+I.lo≤(y.compute j).hi at hh
    change I.lo-E≤(y.compute j).hi
    grind only
  · intro i j
    have hh := h.2 i j
    change (y.compute i).lo≤E+I.hi at hh
    change (y.compute i).lo≤I.hi+E
    grind only

theorem weaken {x : RealCompute} {I J : QInterval} (h : InInterval x I)
    (hIJ : J.ContainsInterval I) : InInterval x J := by
  constructor
  · intro i j
    have hh := h.1 i j
    change I.lo≤(x.compute j).hi at hh
    exact Rat.le_trans hIJ.1 hh
  · intro i j
    have hh := h.2 i j
    change (x.compute i).lo≤I.hi at hh
    exact Rat.le_trans hh hIJ.2

end ComputableAnalysis.RealIntervalImage


