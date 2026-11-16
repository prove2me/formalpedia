-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralLinearity
-- name    : liuyao_ca_fd889115_k1_Analysis_IntegralLinearity
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:57:41.062017+00:00
-- url     : https://prove2.me/theorems/d38e1aa9-3115-491e-8a7d-2ec05784cae9
-- title:
--   Computable analysis · IntegralLinearity · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/IntegralLinearity.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralOrder

set_option autoImplicit true

/-! Finite three-partition comparisons for linearity of independently supplied
integrals. Every comparison is made through actual interval intersections. -/
namespace ComputableAnalysis.Integral
open RectangleOverlap
set_option maxHeartbeats 1000000

namespace TripleOverlap

def weight {a b : Rat} (P Q R : RationalPartition a b) (i j k : Nat) : Rat :=
  let l := maxRat2 (P.point i) (maxRat2 (Q.point j) (R.point k))
  let u := minRat (P.point (i+1)) (minRat (Q.point (j+1)) (R.point (k+1)))
  if l≤u then u-l else 0

theorem nonnegative {a b : Rat} (P Q R : RationalPartition a b) (i j k : Nat) :
    0≤weight P Q R i j k := by
  dsimp only [weight]
  split <;> grind only

theorem swap_last {a b : Rat} (P Q R : RationalPartition a b) (i j k : Nat) :
    weight P Q R i j k=weight P R Q i k j := by
  have hm : maxRat2 (Q.point j) (R.point k)=maxRat2 (R.point k) (Q.point j) := by
    grind [maxRat2]
  have hn : minRat (Q.point (j+1)) (R.point (k+1))=minRat (R.point (k+1)) (Q.point (j+1)) := by
    grind [minRat]
  simp only [weight,hm,hn]

theorem length_form {a b : Rat} (P Q R : RationalPartition a b) (i j k : Nat) :
    weight P Q R i j k=length (maxRat2 (P.point i) (Q.point j))
      (minRat (P.point (i+1)) (Q.point (j+1))) (R.point k) (R.point (k+1)) := by
  grind [weight,length,maxRat2,minRat]

theorem sum_third {a b : Rat} (P Q R : RationalPartition a b) (i j : Nat)
    (hi : i<P.pieces) (hj : j<Q.pieces) :
    rectangleSum (weight P Q R i j) R.pieces=RectangleOverlap.weight P Q i j := by
  let l := maxRat2 (P.point i) (Q.point j)
  let u := minRat (P.point (i+1)) (Q.point (j+1))
  have hpa := P.point_in_bounds (Nat.le_of_lt hi)
  have hpb := P.point_in_bounds (Nat.succ_le_of_lt hi)
  have hqa := Q.point_in_bounds (Nat.le_of_lt hj)
  have hqb := Q.point_in_bounds (Nat.succ_le_of_lt hj)
  have hl : a≤l := by dsimp [l,maxRat2]; split <;> grind only
  have hu : u≤b := by dsimp [u,minRat]; split <;> grind only
  by_cases h : l≤u
  · have hs : rectangleSum (weight P Q R i j) R.pieces=
        rectangleSum (fun k => clamp l u (R.point (k+1))-clamp l u (R.point k)) R.pieces := by
      apply rectangleSum_congr
      intro k hk
      rw [length_form]
      exact length_clamp l u _ _ h (R.monotone k (k+1) (by omega) (by omega))
    rw [hs,rectangleSum_telescope (fun k => clamp l u (R.point k)),R.left_endpoint,R.right_endpoint,
      clamp_high l u b h hu,clamp_low l u a h hl]
    exact (if_pos h).symm
  · have hz : rectangleSum (weight P Q R i j) R.pieces=0 := by
      have he : rectangleSum (weight P Q R i j) R.pieces=rectangleSum (fun _ => 0) R.pieces := by
        apply rectangleSum_congr
        intro k hk
        rw [length_form]
        change length l u _ _=0
        grind [length,maxRat2,minRat]
      rw [he,rectangleSum_zero]
    rw [hz]
    exact (if_neg h).symm

theorem point_mem {a b : Rat} (P Q R : RationalPartition a b) (i j k : Nat)
    (h : 0<weight P Q R i j k) :
    let x := maxRat2 (P.point i) (maxRat2 (Q.point j) (R.point k))
    (P.point i≤x ∧ x≤P.point (i+1)) ∧
    (Q.point j≤x ∧ x≤Q.point (j+1)) ∧
    (R.point k≤x ∧ x≤R.point (k+1)) := by
  grind [weight,maxRat2,minRat]

def sum {a b : Rat} (P Q R : RationalPartition a b) (v : Nat → Nat → Nat → Rat) : Rat :=
  rectangleSum (fun i => rectangleSum (fun j => rectangleSum (v i j) R.pieces) Q.pieces) P.pieces

theorem sum_first {a b : Rat} (P Q R : RationalPartition a b) (c : Nat → Rat) :
    sum P Q R (fun i j k => weight P Q R i j k*c i)=
      rectangleSum (fun i => (P.point (i+1)-P.point i)*c i) P.pieces := by
  apply rectangleSum_congr
  intro i hi
  have hs : rectangleSum (fun j => rectangleSum (fun k => weight P Q R i j k*c i) R.pieces) Q.pieces=
      rectangleSum (fun j => RectangleOverlap.weight P Q i j*c i) Q.pieces := by
    apply rectangleSum_congr
    intro j hj
    rw [rectangleSum_scale,sum_third P Q R i j hi hj]
  rw [hs,rectangleSum_scale,RectangleOverlap.row_sum P Q i hi]

theorem sum_second {a b : Rat} (P Q R : RationalPartition a b) (c : Nat → Rat) :
    sum P Q R (fun i j k => weight P Q R i j k*c j)=
      rectangleSum (fun j => (Q.point (j+1)-Q.point j)*c j) Q.pieces := by
  have hs : sum P Q R (fun i j k => weight P Q R i j k*c j)=
      rectangleSum (fun i => rectangleSum (fun j => RectangleOverlap.weight P Q i j*c j) Q.pieces) P.pieces := by
    apply rectangleSum_congr
    intro i hi
    apply rectangleSum_congr
    intro j hj
    rw [rectangleSum_scale,sum_third P Q R i j hi hj]
  rw [hs,rectangleSum_swap]
  apply rectangleSum_congr
  intro j hj
  rw [rectangleSum_scale,RectangleOverlap.column_sum P Q j hj]

theorem sum_third_coordinate {a b : Rat} (P Q R : RationalPartition a b) (c : Nat → Rat) :
    sum P Q R (fun i j k => weight P Q R i j k*c k)=
      rectangleSum (fun k => (R.point (k+1)-R.point k)*c k) R.pieces := by
  have he : sum P Q R (fun i j k => weight P Q R i j k*c k)=
      sum P R Q (fun i k j => weight P R Q i k j*c k) := by
    apply rectangleSum_congr
    intro i hi
    rw [rectangleSum_swap]
    apply rectangleSum_congr
    intro k hk
    apply rectangleSum_congr
    intro j hj
    dsimp only
    rw [swap_last]
  rw [he,sum_second]

theorem sum_add {a b : Rat} (P Q R : RationalPartition a b)
    (v w : Nat → Nat → Nat → Rat) :
    sum P Q R (fun i j k => v i j k+w i j k)=sum P Q R v+sum P Q R w := by
  unfold sum
  rw [← rectangleSum_add]
  apply rectangleSum_congr
  intro i hi
  rw [← rectangleSum_add]
  apply rectangleSum_congr
  intro j hj
  exact rectangleSum_add _ _ _

theorem sum_mono {a b : Rat} (P Q R : RationalPartition a b)
    (v w : Nat → Nat → Nat → Rat)
    (h : ∀ i,i<P.pieces → ∀ j,j<Q.pieces → ∀ k,k<R.pieces → v i j k≤w i j k) :
    sum P Q R v≤sum P Q R w := by
  apply rectangleSum_mono
  intro i hi
  apply rectangleSum_mono
  intro j hj
  apply rectangleSum_mono
  intro k hk
  exact h i hi j hj k hk

end TripleOverlap

/-- Finite lower/upper comparison for a pointwise sum, using three independent
partitions. Zero-length intersections contribute zero and need no sample. -/
theorem Bounds.add_comparison {F G H : FunctionOnInterval}
    (hlG : F.lower=G.lower) (huG : F.upper=G.upper)
    (hlH : F.lower=H.lower) (huH : F.upper=H.upper)
    (A : Bounds F) (B : Bounds G) (C : Bounds H)
    (hsum : ∀ x (hf : inDomainInterval F.lower F.upper x)
      (hg : inDomainInterval G.lower G.upper x) (hh : inDomainInterval H.lower H.upper x),
      (StrictMonotoneInverse.sample H x hh).Equiv
        (RealCompute.add (StrictMonotoneInverse.sample F x hf) (StrictMonotoneInverse.sample G x hg))) :
    A.lowerSum+B.lowerSum≤C.upperSum ∧ C.lowerSum≤A.upperSum+B.upperSum := by
  let P := A.partition
  let Q : RationalPartition F.lower F.upper := { B.partition with
    left_endpoint := B.partition.left_endpoint.trans hlG.symm
    right_endpoint := B.partition.right_endpoint.trans huG.symm }
  let R : RationalPartition F.lower F.upper := { C.partition with
    left_endpoint := C.partition.left_endpoint.trans hlH.symm
    right_endpoint := C.partition.right_endpoint.trans huH.symm }
  let w := TripleOverlap.weight P Q R
  have cell : ∀ i,i<P.pieces → ∀ j,j<Q.pieces → ∀ k,k<R.pieces →
      w i j k*(A.lower i+B.lower j)≤w i j k*C.upper k ∧
      w i j k*C.lower k≤w i j k*(A.upper i+B.upper j) := by
    intro i hi j hj k hk
    have hw : 0≤w i j k := TripleOverlap.nonnegative P Q R i j k
    by_cases hp : 0<w i j k
    · let x := maxRat2 (P.point i) (maxRat2 (Q.point j) (R.point k))
      have hx := TripleOverlap.point_mem P Q R i j k hp
      have hxp : (P.cell i hi).contains x := hx.1
      have hxq : (B.partition.cell j hj).contains x := hx.2.1
      have hxr : (C.partition.cell k hk).contains x := hx.2.2
      let hF := (P.cell i hi).contains_inDomain hxp
      let hG := (B.partition.cell j hj).contains_inDomain hxq
      let hH := (C.partition.cell k hk).contains_inDomain hxr
      let f := StrictMonotoneInverse.sample F x hF
      let g := StrictMonotoneInverse.sample G x hG
      let h := StrictMonotoneInverse.sample H x hH
      have vf := StrictMonotoneInverse.sample_valid F x hF
      have vg := StrictMonotoneInverse.sample_valid G x hG
      have vh := StrictMonotoneInverse.sample_valid H x hH
      have vs := RealCompute.add_valid vf vg
      have he : h.Equiv (f+g) := hsum x hF hG hH
      have ls : (RealCompute.ofRat (A.lower i+B.lower j)).Le (f+g) := by
        intro n m
        exact rat_add_le_add (A.lower_le i hi x hxp m) (B.lower_le j hj x hxq m)
      have us : (f+g).Le (RealCompute.ofRat (A.upper i+B.upper j)) := by
        intro n m
        exact rat_add_le_add (A.upper_ge i hi x hxp n) (B.upper_ge j hj x hxq n)
      have lh : (RealCompute.ofRat (C.lower k)).Le h := fun _ m => C.lower_le k hk x hxr m
      have uh : h.Le (RealCompute.ofRat (C.upper k)) := fun n _ => C.upper_ge k hk x hxr n
      have lo := RealCompute.le_trans vh
        (RealCompute.le_trans vs ls (RealCompute.le_of_equiv vs vh (RealCompute.equiv_symm he))) uh 0 0
      have up := RealCompute.le_trans vs
        (RealCompute.le_trans vh lh (RealCompute.le_of_equiv vh vs he)) us 0 0
      exact ⟨Rat.mul_le_mul_of_nonneg_left lo hw,Rat.mul_le_mul_of_nonneg_left up hw⟩
    · have hz : w i j k=0 := by grind only
      simp only [hz,Rat.zero_mul]
      exact ⟨Rat.le_refl,Rat.le_refl⟩
  have lower := TripleOverlap.sum_mono P Q R
    (fun i j k => w i j k*(A.lower i+B.lower j)) (fun i j k => w i j k*C.upper k)
    (fun i hi j hj k hk => (cell i hi j hj k hk).1)
  have upper := TripleOverlap.sum_mono P Q R
    (fun i j k => w i j k*C.lower k) (fun i j k => w i j k*(A.upper i+B.upper j))
    (fun i hi j hj k hk => (cell i hi j hj k hk).2)
  have splitLower : (fun i j k => w i j k*(A.lower i+B.lower j))=
      (fun i j k => w i j k*A.lower i+w i j k*B.lower j) := by funext i j k; grind only
  have splitUpper : (fun i j k => w i j k*(A.upper i+B.upper j))=
      (fun i j k => w i j k*A.upper i+w i j k*B.upper j) := by funext i j k; grind only
  rw [splitLower,TripleOverlap.sum_add,TripleOverlap.sum_first,
    TripleOverlap.sum_second,TripleOverlap.sum_third_coordinate] at lower
  rw [splitUpper,TripleOverlap.sum_add,TripleOverlap.sum_first,
    TripleOverlap.sum_second,TripleOverlap.sum_third_coordinate] at upper
  exact ⟨lower,upper⟩

/-- Linearity for three independently supplied justified integrals. Only the
pointwise sum identity is a hypothesis; the integral identity is derived. -/
theorem HasIntegral.add_identity {F G H : FunctionOnInterval} {I J K : RealCompute}
    (hI : HasIntegral F I) (hJ : HasIntegral G J) (hK : HasIntegral H K)
    (hlG : F.lower=G.lower) (huG : F.upper=G.upper)
    (hlH : F.lower=H.lower) (huH : F.upper=H.upper)
    (hsum : ∀ x (hf : inDomainInterval F.lower F.upper x)
      (hg : inDomainInterval G.lower G.upper x) (hh : inDomainInterval H.lower H.upper x),
      (StrictMonotoneInverse.sample H x hh).Equiv
        (RealCompute.add (StrictMonotoneInverse.sample F x hf) (StrictMonotoneInverse.sample G x hg))) :
    K.Equiv (RealCompute.add I J) := by
  apply RealCompute.le_antisymm
  · intro n m
    change (K.compute n).lo≤(I.compute m).hi+(J.compute m).hi
    by_cases h : (K.compute n).lo≤(I.compute m).hi+(J.compute m).hi
    · exact h
    exfalso
    let eps : QPos := ⟨((K.compute n).lo-((I.compute m).hi+(J.compute m).hi))/4,by
      rw [Rat.div_def]; exact Rat.mul_pos (by grind only) (Rat.inv_pos.mpr (by decide +kernel))⟩
    obtain ⟨A,hA⟩ := hI.tight eps
    obtain ⟨B,hB⟩ := hJ.tight eps
    obtain ⟨C,hC⟩ := hK.tight eps
    have hc := (Bounds.add_comparison hlG huG hlH huH A B C hsum).2
    have hi := (hI.bounds A m).1
    have hj := (hJ.bounds B m).1
    have hk := (hK.bounds C n).2
    dsimp [eps] at hA hB hC
    grind only
  · intro n m
    change (I.compute n).lo+(J.compute n).lo≤(K.compute m).hi
    by_cases h : (I.compute n).lo+(J.compute n).lo≤(K.compute m).hi
    · exact h
    exfalso
    let eps : QPos := ⟨((I.compute n).lo+(J.compute n).lo-(K.compute m).hi)/4,by
      rw [Rat.div_def]; exact Rat.mul_pos (by grind only) (Rat.inv_pos.mpr (by decide +kernel))⟩
    obtain ⟨A,hA⟩ := hI.tight eps
    obtain ⟨B,hB⟩ := hJ.tight eps
    obtain ⟨C,hC⟩ := hK.tight eps
    have hc := (Bounds.add_comparison hlG huG hlH huH A B C hsum).1
    have hi := (hI.bounds A n).2
    have hj := (hJ.bounds B n).2
    have hk := (hK.bounds C m).1
    dsimp [eps] at hA hB hC
    grind only

end ComputableAnalysis.Integral


