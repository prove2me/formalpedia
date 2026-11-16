-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueCongruence
-- name    : liuyao_ca_fd889115_k1_Analysis_RealValueCongruence
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:58:07.750881+00:00
-- url     : https://prove2.me/theorems/51192ab7-5efa-4db6-9490-033edc70886a
-- title:
--   Computable analysis · RealValueCongruence · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RealValueCongruence.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueBounds

set_option autoImplicit true

namespace ComputableAnalysis.RealApproximationOrder
open ComputableCoefficient
abbrev Same (X Y : Value) : Prop := X.real.preferred.Equiv Y.real.preferred
namespace Same

theorem refl (X : Value) : Same X X := RealCompute.equiv_refl _ X.real.valid

theorem symm {X Y : Value} (h : Same X Y) : Same Y X := RealCompute.equiv_symm h

theorem trans {X Y Z : Value} (h : Same X Y) (k : Same Y Z) : Same X Z :=
  RealCompute.equiv_trans X.real.valid Y.real.valid Z.real.valid h k

theorem add {X Y U V : Value} (h : Same X Y) (k : Same U V) : Same (Value.add X U) (Value.add Y V) :=
  RealCompute.add_equiv X.real.valid Y.real.valid U.real.valid V.real.valid h k

theorem mul {X Y U V : Value} (h : Same X Y) (k : Same U V) : Same (Value.mul X U) (Value.mul Y V) :=
  RealCompute.mul_equiv X.real.valid Y.real.valid U.real.valid V.real.valid h k

theorem sub {X Y U V : Value} (h : Same X Y) (k : Same U V) : Same (RealApproximationOrder.sub X U) (RealApproximationOrder.sub Y V) :=
  RealCompute.sub_equiv X.real.valid Y.real.valid U.real.valid V.real.valid h k

theorem neg {X Y : Value} (h : Same X Y) : Same (Value.neg X) (Value.neg Y) :=
  RealCompute.neg_equiv h

theorem scale {X Y : Value} (h : Same X Y) (c : Rat) : Same (RealApproximationOrder.scale c X) (RealApproximationOrder.scale c Y) :=
  RealCompute.scaleRat_equiv h

end Same
/-- A zero absolute error identifies the two represented values. -/
theorem small_sub_zero_same {x y : Value} (h : Small (sub x y) 0) : Same x y := by
  apply RealCompute.equiv_of_le_of_ge
  · intro i j
    let k := max i j
    have hx := x.real.valid.2.1 i k (Nat.le_max_left _ _)
    have hy := y.real.valid.2.1 j k (Nat.le_max_right _ _)
    have hk := h.2 k 0
    change (x.real.preferred.compute k).lo - (y.real.preferred.compute k).hi ≤ 0 at hk
    grind only
  · intro i j
    let k := max i j
    have hy := y.real.valid.2.1 i k (Nat.le_max_left _ _)
    have hx := x.real.valid.2.1 j k (Nat.le_max_right _ _)
    have hk := h.1 0 k
    change -(0 : Rat) ≤ (x.real.preferred.compute k).hi - (y.real.preferred.compute k).lo at hk
    grind only

end ComputableAnalysis.RealApproximationOrder


