-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralScaling
-- name    : liuyao_ca_fd889115_k1_Analysis_IntegralScaling
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:57:44.533847+00:00
-- url     : https://prove2.me/theorems/bd8b0464-3142-4483-9653-7d83acafd803
-- title:
--   Computable analysis · IntegralScaling · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/IntegralScaling.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralOrder

set_option autoImplicit true

/-! Rational scaling for independently supplied proper integrals, including
negative scalars. Finite interval bounds are scaled and their errors controlled;
the desired integral identity is never supplied as certificate data. -/
namespace ComputableAnalysis.Integral
set_option maxHeartbeats 1000000

private def scaledBounds {F G : FunctionOnInterval} (r : Rat)
    (h : F.PointwiseScaleRat r G) (A : Bounds F) : Bounds G where
  partition := { A.partition with
    left_endpoint := A.partition.left_endpoint.trans h.1
    right_endpoint := A.partition.right_endpoint.trans h.2.1 }
  lower k := if 0≤r then r*A.lower k else r*A.upper k
  upper k := if 0≤r then r*A.upper k else r*A.lower k
  lower_le := by
    intro k hk x hx n
    let hf := (A.partition.cell k hk).contains_inDomain hx
    let hg : inDomainInterval G.lower G.upper x := by rw [← h.1,← h.2.1]; exact hf
    let f := StrictMonotoneInverse.sample F x hf
    let g := StrictMonotoneInverse.sample G x hg
    have vf := StrictMonotoneInverse.sample_valid F x hf
    have vg := StrictMonotoneInverse.sample_valid G x hg
    have vs := RealCompute.scaleRat_valid (r := r) vf
    have he : g.Equiv (RealCompute.scaleRat r f) := h.2.2 x hf hg
    have low : (RealCompute.ofRat (if 0≤r then r*A.lower k else r*A.upper k)).Le
        (RealCompute.scaleRat r f) := by
      intro i j
      dsimp [RealCompute.scaleRat,RealCompute.scaleRatCompute]
      split
      · exact Rat.mul_le_mul_of_nonneg_left (A.lower_le k hk x hx j) ‹_›
      · have hu := A.upper_ge k hk x hx j
        change r*A.upper k≤r*(F.compute x hf j).lo
        have hm := Rat.mul_le_mul_of_nonneg_left hu (show 0≤ -r by grind)
        grind only
    exact RealCompute.le_trans vs low (RealCompute.le_of_equiv vs vg (RealCompute.equiv_symm he)) 0 n
  upper_ge := by
    intro k hk x hx n
    let hf := (A.partition.cell k hk).contains_inDomain hx
    let hg : inDomainInterval G.lower G.upper x := by rw [← h.1,← h.2.1]; exact hf
    let f := StrictMonotoneInverse.sample F x hf
    let g := StrictMonotoneInverse.sample G x hg
    have vf := StrictMonotoneInverse.sample_valid F x hf
    have vg := StrictMonotoneInverse.sample_valid G x hg
    have vs := RealCompute.scaleRat_valid (r := r) vf
    have he : g.Equiv (RealCompute.scaleRat r f) := h.2.2 x hf hg
    have up : (RealCompute.scaleRat r f).Le
        (RealCompute.ofRat (if 0≤r then r*A.upper k else r*A.lower k)) := by
      intro i j
      dsimp [RealCompute.scaleRat,RealCompute.scaleRatCompute]
      split
      · exact Rat.mul_le_mul_of_nonneg_left (A.upper_ge k hk x hx i) ‹_›
      · have hl := A.lower_le k hk x hx i
        change r*(F.compute x hf i).hi≤r*A.lower k
        have hm := Rat.mul_le_mul_of_nonneg_left hl (show 0≤ -r by grind)
        grind only
    exact RealCompute.le_trans vs (RealCompute.le_of_equiv vg vs he) up n 0

private theorem weighted_scale {a b : Rat} (P : RationalPartition a b) (c : Nat → Rat) (r : Rat) :
    rectangleSum (fun k => (P.point (k+1)-P.point k)*(r*c k)) P.pieces=
      r*rectangleSum (fun k => (P.point (k+1)-P.point k)*c k) P.pieces := by
  have he : (fun k => (P.point (k+1)-P.point k)*(r*c k))=
      (fun k => ((P.point (k+1)-P.point k)*c k)*r) := by funext k; grind only
  rw [he,rectangleSum_scale,Rat.mul_comm]

private theorem scaled_sums {F G : FunctionOnInterval} (r : Rat)
    (h : F.PointwiseScaleRat r G) (A : Bounds F) :
    (scaledBounds r h A).lowerSum=(if 0≤r then r*A.lowerSum else r*A.upperSum) ∧
    (scaledBounds r h A).upperSum=(if 0≤r then r*A.upperSum else r*A.lowerSum) := by
  by_cases hr : 0≤r
  · simp only [Bounds.lowerSum,Bounds.upperSum,scaledBounds,if_pos hr]
    exact ⟨weighted_scale _ _ _,weighted_scale _ _ _⟩
  · simp only [Bounds.lowerSum,Bounds.upperSum,scaledBounds,if_neg hr]
    exact ⟨weighted_scale _ _ _,weighted_scale _ _ _⟩

private theorem scaled_encloses {F G : FunctionOnInterval} {I : RealCompute}
    (hI : HasIntegral F I) (r : Rat) (h : F.PointwiseScaleRat r G) (A : Bounds F) :
    (scaledBounds r h A).Encloses (RealCompute.scaleRat r I) := by
  intro n
  have hi := hI.bounds A n
  rw [(scaled_sums r h A).1,(scaled_sums r h A).2]
  dsimp [RealCompute.scaleRat,RealCompute.scaleRatCompute]
  split
  · exact ⟨Rat.mul_le_mul_of_nonneg_left hi.1 ‹_›,Rat.mul_le_mul_of_nonneg_left hi.2 ‹_›⟩
  · have h1 := Rat.mul_le_mul_of_nonneg_left hi.2 (show 0≤ -r by grind)
    have h2 := Rat.mul_le_mul_of_nonneg_left hi.1 (show 0≤ -r by grind)
    constructor <;> grind only

/-- Scaling holds for arbitrary valid represented integrands and values.
Only the scalar is rational in this public law. -/
theorem HasIntegral.scaleRat_identity {F G : FunctionOnInterval} {I J : RealCompute}
    (hI : HasIntegral F I) (hJ : HasIntegral G J) (r : Rat) (h : F.PointwiseScaleRat r G) :
    J.Equiv (RealCompute.scaleRat r I) := by
  have comparison : ∀ eps : QPos, ∃ B : Bounds G,
      B.upperSum-B.lowerSum≤eps.val ∧ B.Encloses (RealCompute.scaleRat r I) := by
    intro eps
    let tol : QPos := ⟨eps.val/(qabs r+1),by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by have := qabs_nonneg r; grind))⟩
    obtain ⟨A,hA⟩ := hI.tight tol
    refine ⟨scaledBounds r h A,?_,scaled_encloses hI r h A⟩
    have sums := scaled_sums r h A
    rw [sums.1,sums.2]
    have hab := A.lowerSum_le_upperSum A
    have habs := qabs_nonneg r
    have hmul := Rat.mul_le_mul_of_nonneg_left hA habs
    have hc := Rat.mul_inv_cancel (qabs r+1) (show qabs r+1≠0 by grind)
    have he : qabs r*tol.val≤eps.val := by
      have hm := Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt (Rat.inv_pos.mpr (show 0<qabs r+1 by grind)))
      dsimp [tol]
      simp only [Rat.div_def]
      calc
        qabs r*(eps.val*(qabs r+1)⁻¹)≤(qabs r+1)*(eps.val*(qabs r+1)⁻¹) :=
          Rat.mul_le_mul_of_nonneg_right (by grind only) hm
        _=eps.val := by grind only
    by_cases hr : 0≤r
    · rw [if_pos hr,qabs_eq_self_of_nonneg hr] at *
      grind only
    · rw [if_neg hr]
      have heq : qabs r= -r := qabs_eq_neg_of_nonpos (by grind)
      rw [heq] at hmul he
      grind only
  have le : ∀ (X Y : RealCompute),
      (∀ B : Bounds G,B.Encloses X) →
      (∀ eps : QPos,∃ B : Bounds G,B.upperSum-B.lowerSum≤eps.val ∧ B.Encloses Y) → X.Le Y := by
    intro X Y hX hY n m
    by_cases h : (X.compute n).lo≤(Y.compute m).hi
    · exact h
    exfalso
    let eps : QPos := ⟨((X.compute n).lo-(Y.compute m).hi)/2,by grind only⟩
    obtain ⟨B,hB,hBY⟩ := hY eps
    have hx := (hX B n).2
    have hy := (hBY m).1
    dsimp [eps] at hB
    grind only
  apply RealCompute.le_antisymm
  · exact le J _ hJ.bounds comparison
  · intro n m
    by_cases h : ((RealCompute.scaleRat r I).compute n).lo≤(J.compute m).hi
    · exact h
    exfalso
    let eps : QPos := ⟨(((RealCompute.scaleRat r I).compute n).lo-(J.compute m).hi)/2,by grind only⟩
    obtain ⟨B,hB,hBI⟩ := comparison eps
    have hi := (hBI n).2
    have hj := (hJ.bounds B m).1
    dsimp [eps] at hB
    grind only

end ComputableAnalysis.Integral


