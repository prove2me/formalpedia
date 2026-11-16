-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCFromSupportingSlopes
-- name    : liuyao_ca_fd889115_k1_Analysis_FTCFromSupportingSlopes
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:10:57.861762+00:00
-- url     : https://prove2.me/theorems/5466ea3b-0b1a-432f-923f-f590b1ce4f87
-- title:
--   Computable analysis · FTCFromSupportingSlopes · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FTCFromSupportingSlopes.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCRealCalculus

set_option autoImplicit true

/-! A quantitative FTC step from convex supporting increments and a proved
Lipschitz bound for the supplied derivative. -/
namespace ComputableAnalysis.FTCRealCalculus
open ComputableCoefficient RealApproximationOrder FTCRealOrder
set_option maxHeartbeats 600000

/-- Supporting increments are finite order data, with no integral identity
in their hypotheses. Lipschitz shrinking supplies the quadratic error. -/
def Step.ofSupportingIncrements (f d : Rat → Value) (a b K : Rat) (hK : 0≤K)
    (lip : LipschitzIntegralBounds.Lipschitz d a b K)
    (supports : ∀ u v,a≤u → u<v → v≤b →
      LE (RealApproximationOrder.scale (v-u) (d u)) (sub (f v) (f u)) ∧
      LE (sub (f v) (f u)) (RealApproximationOrder.scale (v-u) (d v))) : Step f d a b where
  error := K
  error_nonnegative := hK
  radius := ⟨1,by decide⟩
  variation := K
  variation_nonnegative := hK
  lipschitz := lip
  firstOrder := by
    intro u v hu huv hv _
    let L := RealApproximationOrder.scale (v-u) (d u)
    let I := sub (f v) (f u)
    let E := sub I L
    have hh : 0≤v-u := Rat.le_of_lt (by grind only)
    have sup := supports u v hu huv hv
    have self : LE (Value.neg L) (Value.neg L) := RealCompute.le_refl _ (Value.neg L).real.valid
    have lower := le_add sup.1 self
    have upper := le_add sup.2 self
    have eL : (Value.add L (Value.neg L)).real.preferred.Equiv (Value.rational 0).real.preferred := by
      apply arithmetic_identity; intro s; simp only [Value.add,Value.neg,Value.rational]; grind only
    have eI : (Value.add I (Value.neg L)).real.preferred.Equiv E.real.preferred := by
      apply arithmetic_identity; intro s; simp only [E,Value.add,Value.neg,sub]; grind only
    have eU : (Value.add (RealApproximationOrder.scale (v-u) (d v)) (Value.neg L)).real.preferred.Equiv
        (RealApproximationOrder.scale (v-u) (sub (d v) (d u))).real.preferred := by
      apply arithmetic_identity; intro s; simp only [Value.add,Value.neg,sub,RealApproximationOrder.scale,L]; grind only
    have low := le_congr lower eL eI
    have high := le_congr upper eI eU
    have hd := le_scale (x := sub (d v) (d u)) (y := Value.rational (K*(v-u)))
      (lip u v hu (Rat.le_of_lt huv) hv).2 hh
    have hQ : LE (RealApproximationOrder.scale (v-u) (Value.rational (K*(v-u)))) (Value.rational (K*(v-u)*(v-u))) := by
      apply RealCompute.le_of_equiv (y := RealCompute.ofRat (K*(v-u)*(v-u))) (RealApproximationOrder.scale (v-u) (Value.rational (K*(v-u)))).real.valid
        (RealCompute.ofRat_valid _)
      apply arithmetic_identity _ (Value.rational (K*(v-u)*(v-u)))
      intro s
      simp only [RealApproximationOrder.scale,Value.rational]
      grind only
    have hb : 0≤K*(v-u)*(v-u) := Rat.mul_nonneg (Rat.mul_nonneg hK hh) hh
    constructor
    · exact RealCompute.le_trans (y := RealCompute.ofRat 0) (RealCompute.ofRat_valid 0) (fun _ _ => by change -(K*(v-u)*(v-u))≤0; grind only) low
    · exact RealCompute.le_trans (RealApproximationOrder.scale (v-u) (sub (d v) (d u))).real.valid high
        (RealCompute.le_trans (RealApproximationOrder.scale (v-u) (Value.rational (K*(v-u)))).real.valid hd hQ)

end ComputableAnalysis.FTCRealCalculus


