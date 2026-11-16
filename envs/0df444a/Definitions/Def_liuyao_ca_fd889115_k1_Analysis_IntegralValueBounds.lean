-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralValueBounds
-- name    : liuyao_ca_fd889115_k1_Analysis_IntegralValueBounds
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:54:03.101115+00:00
-- url     : https://prove2.me/theorems/8c59a405-8a4d-4ba2-a2af-0111bcd61041
-- title:
--   Computable analysis · IntegralValueBounds · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/IntegralValueBounds.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralBoundsComparison

set_option autoImplicit true

/-! Constant bounds for supplied integral witnesses, proved by replacing
one side of an actual rectangle-bound family and telescoping its lengths. -/
namespace ComputableAnalysis.Integral
set_option maxHeartbeats 1000000

theorem HasIntegral.lower_bound {F : FunctionOnInterval} {I : RealCompute} (hI : HasIntegral F I) (c : Rat)
    (hc : ∀ x (hx : inDomainInterval F.lower F.upper x) n,c≤(F.compute x hx n).hi) :
    (RealCompute.ofRat ((F.upper-F.lower)*c)).Le I := by
  obtain ⟨B,_⟩ := hI.tight ⟨1,by decide +kernel⟩
  let A : Bounds F := {
    partition := B.partition
    lower := fun _ => c
    upper := B.upper
    lower_le := fun k hk x hx n => hc x ((B.partition.cell k hk).contains_inDomain hx) n
    upper_ge := B.upper_ge }
  have hs : A.lowerSum=(F.upper-F.lower)*c := by
    change rectangleSum (fun k => (B.partition.point (k+1)-B.partition.point k)*c) B.partition.pieces=_
    rw [rectangleSum_scale,rectangleSum_telescope,B.partition.right_endpoint,B.partition.left_endpoint]
  intro n m
  have h := (hI.bounds A m).1
  rw [hs] at h
  exact h

theorem HasIntegral.upper_bound {F : FunctionOnInterval} {I : RealCompute} (hI : HasIntegral F I) (c : Rat)
    (hc : ∀ x (hx : inDomainInterval F.lower F.upper x) n,(F.compute x hx n).lo≤c) :
    I.Le (RealCompute.ofRat ((F.upper-F.lower)*c)) := by
  obtain ⟨B,_⟩ := hI.tight ⟨1,by decide +kernel⟩
  let A : Bounds F := {
    partition := B.partition
    lower := B.lower
    upper := fun _ => c
    lower_le := B.lower_le
    upper_ge := fun k hk x hx n => hc x ((B.partition.cell k hk).contains_inDomain hx) n }
  have hs : A.upperSum=(F.upper-F.lower)*c := by
    change rectangleSum (fun k => (B.partition.point (k+1)-B.partition.point k)*c) B.partition.pieces=_
    rw [rectangleSum_scale,rectangleSum_telescope,B.partition.right_endpoint,B.partition.left_endpoint]
  intro n m
  have h := (hI.bounds A n).2
  rw [hs] at h
  exact h

theorem HasIntegral.nonnegative {F : FunctionOnInterval} {I : RealCompute} (hI : HasIntegral F I)
    (hc : ∀ x (hx : inDomainInterval F.lower F.upper x) n,0≤(F.compute x hx n).hi) :
    (RealCompute.ofRat 0).Le I := by
  have h := hI.lower_bound 0 hc
  simpa only [Rat.mul_zero] using h

end ComputableAnalysis.Integral


