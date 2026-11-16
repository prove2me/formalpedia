-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralOrder
-- name    : liuyao_ca_fd889115_k1_Analysis_IntegralOrder
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:57:16.471211+00:00
-- url     : https://prove2.me/theorems/ea9e1a72-e22d-442f-b3db-351cc19759da
-- title:
--   Computable analysis · IntegralOrder · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/IntegralOrder.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralBoundsComparison
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_StrictMonotoneInverse

set_option autoImplicit true

/-! Order of independently supplied integral witnesses. Independent partitions
are compared by their actual overlap lengths; no common partition, subdivision
schedule, or integral-order conclusion is supplied as data. -/
namespace ComputableAnalysis.Integral
set_option maxHeartbeats 1000000

theorem Bounds.lowerSum_le_upperSum_of_le {F G : FunctionOnInterval}
    (hl : F.lower=G.lower) (hu : F.upper=G.upper) (A : Bounds F) (B : Bounds G)
    (hfg : ∀ x (hx : inDomainInterval F.lower F.upper x)
      (hy : inDomainInterval G.lower G.upper x),
      (StrictMonotoneInverse.sample F x hx).Le (StrictMonotoneInverse.sample G x hy)) :
    A.lowerSum≤B.upperSum := by
  let P := A.partition
  let Q : RationalPartition F.lower F.upper := { B.partition with
    left_endpoint := B.partition.left_endpoint.trans hl.symm
    right_endpoint := B.partition.right_endpoint.trans hu.symm }
  let w := RectangleOverlap.weight P Q
  have cell_order : ∀ i,i<P.pieces → ∀ j,j<Q.pieces → w i j*A.lower i≤w i j*B.upper j := by
    intro i hi j hj
    have hw : 0≤w i j := RectangleOverlap.length_nonnegative _ _ _ _
    by_cases hp : 0<w i j
    · let x := RectangleOverlap.point (P.point i) (Q.point j)
      have hx := RectangleOverlap.point_mem (P.point i) (P.point (i+1)) (Q.point j) (Q.point (j+1)) hp
      have hxp : (P.cell i hi).contains x := hx.1
      have hxq : (B.partition.cell j hj).contains x := hx.2
      let raw : RealCompute := {compute := F.compute x ((P.cell i hi).contains_inDomain hxp)}
      have hv : raw.Valid := F.valid_on x (F.defined_on x ((P.cell i hi).contains_inDomain hxp))
      have hl : (RealCompute.ofRat (A.lower i)).Le raw := by
        intro n m
        exact A.lower_le i hi x hxp m
      let hF := (P.cell i hi).contains_inDomain hxp
      let hG := (B.partition.cell j hj).contains_inDomain hxq
      have hGvalid := StrictMonotoneInverse.sample_valid G x hG
      have hUpper : (StrictMonotoneInverse.sample G x hG).Le (RealCompute.ofRat (B.upper j)) := by
        intro n m
        exact B.upper_ge j hj x hxq n
      have hc := RealCompute.le_trans hGvalid (RealCompute.le_trans hv hl (hfg x hF hG)) hUpper 0 0
      change A.lower i≤B.upper j at hc
      exact Rat.mul_le_mul_of_nonneg_left hc hw
    · have hz : w i j=0 := by grind only
      rw [hz,Rat.zero_mul,Rat.zero_mul]
      exact Rat.le_refl
  have hA : A.lowerSum=rectangleSum (fun i => rectangleSum (fun j => w i j*A.lower i) Q.pieces) P.pieces := by
    apply rectangleSum_congr
    intro i hi
    have hrow := RectangleOverlap.row_sum P Q i hi
    change (P.point (i+1)-P.point i)*A.lower i=rectangleSum (fun j => w i j*A.lower i) Q.pieces
    rw [←hrow]
    exact (rectangleSum_scale (w i) (A.lower i) Q.pieces).symm
  have hB : B.upperSum=rectangleSum (fun j => rectangleSum (fun i => w i j*B.upper j) P.pieces) Q.pieces := by
    apply rectangleSum_congr
    intro j hj
    have hcol := RectangleOverlap.column_sum P Q j hj
    change (Q.point (j+1)-Q.point j)*B.upper j=rectangleSum (fun i => w i j*B.upper j) P.pieces
    rw [←hcol]
    exact (rectangleSum_scale (fun i => w i j) (B.upper j) P.pieces).symm
  rw [hA,hB,←rectangleSum_swap (fun i j => w i j*B.upper j) P.pieces Q.pieces]
  apply rectangleSum_mono
  intro i hi
  apply rectangleSum_mono
  intro j hj
  exact cell_order i hi j hj


/-- Pointwise order implies order of any two supplied proper integral values. -/
theorem HasIntegral.mono {F G : FunctionOnInterval} {I J : RealCompute}
    (hI : HasIntegral F I) (hJ : HasIntegral G J)
    (hl : F.lower=G.lower) (hu : F.upper=G.upper)
    (hfg : ∀ x (hx : inDomainInterval F.lower F.upper x)
      (hy : inDomainInterval G.lower G.upper x),
      (StrictMonotoneInverse.sample F x hx).Le (StrictMonotoneInverse.sample G x hy)) : I.Le J := by
  intro n m
  by_cases h : (I.compute n).lo≤(J.compute m).hi
  · exact h
  exfalso
  let eps : QPos := ⟨((I.compute n).lo-(J.compute m).hi)/4,by
    rw [Rat.div_def]
    exact Rat.mul_pos (by grind only) (Rat.inv_pos.mpr (by decide +kernel))⟩
  obtain ⟨A,hA⟩ := hI.tight eps
  obtain ⟨B,hB⟩ := hJ.tight eps
  have hc := Bounds.lowerSum_le_upperSum_of_le hl hu A B hfg
  have hi := (hI.bounds A n).2
  have hj := (hJ.bounds B m).1
  dsimp [eps] at hA hB
  grind only

end ComputableAnalysis.Integral


