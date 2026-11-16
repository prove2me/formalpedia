-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralBoundsComparison
-- name    : liuyao_ca_fd889115_k1_Analysis_IntegralBoundsComparison
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:53:40.002866+00:00
-- url     : https://prove2.me/theorems/199abcbf-3fe0-4722-8a3a-bf69edd9e964
-- title:
--   Computable analysis · IntegralBoundsComparison · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/IntegralBoundsComparison.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralSpecification

set_option autoImplicit true

/-! Finite comparison of independently supplied rectangle bounds. Overlap
lengths form an explicit rational matrix; its row and column sums recover
the original cell widths. No integral or completed value is assumed. -/
namespace ComputableAnalysis.Integral
set_option maxHeartbeats 1000000

theorem rectangleSum_congr (f g : Nat → Rat) (n : Nat)
    (h : ∀ i,i<n → f i=g i) : rectangleSum f n=rectangleSum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rectangleSum]
    rw [ih (fun i hi => h i (by omega)),h n (by omega)]

theorem rectangleSum_add (f g : Nat → Rat) (n : Nat) :
    rectangleSum (fun i => f i+g i) n=rectangleSum f n+rectangleSum g n := by
  induction n with
  | zero => simp only [rectangleSum]; grind only
  | succ n ih => simp only [rectangleSum,ih]; grind only

theorem rectangleSum_zero (n : Nat) : rectangleSum (fun _ => 0) n=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rectangleSum,ih]; grind only

theorem rectangleSum_swap (f : Nat → Nat → Rat) (m n : Nat) :
    rectangleSum (fun i => rectangleSum (f i) n) m=
      rectangleSum (fun j => rectangleSum (fun i => f i j) m) n := by
  induction m with
  | zero => simpa only [rectangleSum] using (rectangleSum_zero n).symm
  | succ m ih =>
    simp only [rectangleSum]
    rw [rectangleSum_add,ih]

namespace RectangleOverlap

def length (l u v w : Rat) : Rat :=
  if maxRat2 l v≤minRat u w then minRat u w-maxRat2 l v else 0
def point (l v : Rat) : Rat := maxRat2 l v
def clamp (l u x : Rat) : Rat := maxRat2 l (minRat u x)

theorem length_nonnegative (l u v w : Rat) : 0≤length l u v w := by
  unfold length
  split <;> grind only

theorem length_symm (l u v w : Rat) : length l u v w=length v w l u := by
  have hmax : maxRat2 l v=maxRat2 v l := by unfold maxRat2; grind
  have hmin : minRat u w=minRat w u := by unfold minRat; grind
  simp only [length,hmax,hmin]

theorem length_clamp (l u v w : Rat) (hlu : l≤u) (hvw : v≤w) :
    length l u v w=clamp l u w-clamp l u v := by
  grind [length,clamp,maxRat2,minRat]

theorem clamp_low (l u x : Rat) (hlu : l≤u) (hx : x≤l) : clamp l u x=l := by
  grind [clamp,maxRat2,minRat]
theorem clamp_high (l u x : Rat) (hlu : l≤u) (hx : u≤x) : clamp l u x=u := by
  grind [clamp,maxRat2,minRat]

theorem point_mem (l u v w : Rat) (h : 0<length l u v w) :
    (l≤point l v ∧ point l v≤u) ∧ (v≤point l v ∧ point l v≤w) := by
  grind [length,point,maxRat2,minRat]

def weight {a b : Rat} (P Q : RationalPartition a b) (i j : Nat) : Rat :=
  length (P.point i) (P.point (i+1)) (Q.point j) (Q.point (j+1))

theorem row_sum {a b : Rat} (P Q : RationalPartition a b) (i : Nat) (hi : i<P.pieces) :
    rectangleSum (weight P Q i) Q.pieces=P.point (i+1)-P.point i := by
  have hp := P.monotone i (i+1) (by omega) (by omega)
  have he : rectangleSum (weight P Q i) Q.pieces=
      rectangleSum (fun j => clamp (P.point i) (P.point (i+1)) (Q.point (j+1))-
        clamp (P.point i) (P.point (i+1)) (Q.point j)) Q.pieces := by
    apply rectangleSum_congr
    intro j hj
    exact length_clamp _ _ _ _ hp (Q.monotone j (j+1) (by omega) (by omega))
  rw [he,rectangleSum_telescope (fun j => clamp (P.point i) (P.point (i+1)) (Q.point j)) Q.pieces,
    Q.right_endpoint,Q.left_endpoint]
  rw [clamp_high _ _ _ hp (P.cell i hi).upper_mem,
    clamp_low _ _ _ hp (P.cell i hi).lower_mem]

theorem column_sum {a b : Rat} (P Q : RationalPartition a b) (j : Nat) (hj : j<Q.pieces) :
    rectangleSum (fun i => weight P Q i j) P.pieces=Q.point (j+1)-Q.point j := by
  have he : rectangleSum (fun i => weight P Q i j) P.pieces=rectangleSum (weight Q P j) P.pieces := by
    apply rectangleSum_congr
    intro i hi
    exact length_symm _ _ _ _
  rw [he,row_sum Q P j hj]

end RectangleOverlap

/-- Every independent lower rectangle sum is at most every independent
upper rectangle sum, before any integral has been constructed. -/
theorem Bounds.lowerSum_le_upperSum {F : FunctionOnInterval} (A B : Bounds F) :
    A.lowerSum≤B.upperSum := by
  let P := A.partition
  let Q := B.partition
  let w := RectangleOverlap.weight P Q
  have cell_order : ∀ i,i<P.pieces → ∀ j,j<Q.pieces → w i j*A.lower i≤w i j*B.upper j := by
    intro i hi j hj
    have hw : 0≤w i j := RectangleOverlap.length_nonnegative _ _ _ _
    by_cases hp : 0<w i j
    · let x := RectangleOverlap.point (P.point i) (Q.point j)
      have hx := RectangleOverlap.point_mem (P.point i) (P.point (i+1)) (Q.point j) (Q.point (j+1)) hp
      have hxp : (P.cell i hi).contains x := hx.1
      have hxq : (Q.cell j hj).contains x := hx.2
      let raw : RealCompute := {compute := F.compute x ((P.cell i hi).contains_inDomain hxp)}
      have hv : raw.Valid := F.valid_on x (F.defined_on x ((P.cell i hi).contains_inDomain hxp))
      have hl : (RealCompute.ofRat (A.lower i)).Le raw := by
        intro n m
        exact A.lower_le i hi x hxp m
      have hu : raw.Le (RealCompute.ofRat (B.upper j)) := by
        intro n m
        exact B.upper_ge j hj x hxq n
      have hc := RealCompute.le_trans hv hl hu 0 0
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

end ComputableAnalysis.Integral


