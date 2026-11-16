-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueArithmetic
-- name    : liuyao_ca_fd889115_k1_Analysis_RealValueArithmetic
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:57:27.504208+00:00
-- url     : https://prove2.me/theorems/fcd08c0d-cf88-431e-8f1d-7c6531809e76
-- title:
--   Computable analysis · RealValueArithmetic · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RealValueArithmetic.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Numbers
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealReciprocal

set_option autoImplicit true

/-! Exact arithmetic and signed division on mathematical real values.
The reciprocal is defined on the genuine nonzero domain by executable
separation search; no total inverse at zero or representative choice is used. -/
open ComputableAnalysis
namespace ComputableAnalysis.RealComputeQuotient
@[simp] theorem ofRaw_add (x y : RealCompute) (hx : x.Valid) (hy : y.Valid) :
    ofRaw (x+y) (RealCompute.add_valid hx hy)=ofRaw x hx+ofRaw y hy := rfl

@[simp] theorem ofRaw_neg (x : RealCompute) (hx : x.Valid) :
    ofRaw (-x) (RealCompute.neg_valid hx)= -ofRaw x hx := rfl

@[simp] theorem ofRaw_mul (x y : RealCompute) (hx : x.Valid) (hy : y.Valid) :
    ofRaw (x*y) (RealCompute.mul_valid hx hy)=ofRaw x hx*ofRaw y hy := rfl

@[simp] theorem ofRaw_sub (x y : RealCompute) (hx : x.Valid) (hy : y.Valid) :
    ofRaw (x-y) (RealCompute.sub_valid hx hy)=ofRaw x hx-ofRaw y hy := by
  apply Quotient.sound
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  have ho := RealCompute.interval_order_of_valid (x-y) (RealCompute.sub_valid hx hy) n
  change (x.compute n).lo-(y.compute n).hi≤(x.compute n).hi-(y.compute n).lo at ho
  change (x.compute n).lo-(y.compute n).hi≤(x.compute n).hi+(-(y.compute n).lo) ∧
    (x.compute n).lo+(-(y.compute n).hi)≤(x.compute n).hi-(y.compute n).lo
  grind only

@[simp] theorem toComplex_add (x y : Value) : toComplex (x+y) = toComplex x + toComplex y := by
  refine Quotient.inductionOn₂ x y ?_
  intro x y
  apply Quotient.sound
  intro n
  apply (ComplexCompute.compareAt_overlap_iff _ _ n n).2
  have ho := RealCompute.interval_order_of_valid (x.val+y.val) (RealCompute.add_valid x.property y.property) n
  change (x.val.compute n).lo+(y.val.compute n).lo ≤ (x.val.compute n).hi+(y.val.compute n).hi at ho
  change (ComplexCompute.ofRealCompute (RealCompute.add x.val y.val)).compute n |>.Overlaps _
  simpa [QComplex.add,Rat.add_zero,Rat.zero_add,ComplexCompute.ofRealCompute,ComplexCompute.add,QBox.add,QBox.Overlaps,QComplex.le_def,
    RealCompute.addCompute,RealCompute.add] using And.intro (And.intro ho (Rat.le_refl (a:=0)))
      (And.intro ho (Rat.le_refl (a:=0)))
@[simp] theorem toComplex_neg (x : Value) : toComplex (-x) = -toComplex x := by
  refine Quotient.inductionOn x ?_
  intro x
  rfl
@[simp] theorem toComplex_zero : toComplex 0 = 0 := rfl
@[simp] theorem toComplex_one : toComplex 1 = 1 := rfl
@[simp] theorem toComplex_mul (x y : Value) : toComplex (x*y) = toComplex x * toComplex y := by
  refine Quotient.inductionOn₂ x y ?_
  intro x y
  apply Quotient.sound
  intro n
  apply (ComplexCompute.compareAt_overlap_iff _ _ n n).2
  have ho := RealCompute.interval_order_of_valid (x.val*y.val)
    (RealCompute.mul_valid x.property y.property) n
  change (QBox.mulRealInterval (x.val.compute n).lo (x.val.compute n).hi (y.val.compute n).lo (y.val.compute n).hi).lo ≤ (QBox.mulRealInterval (x.val.compute n).lo (x.val.compute n).hi (y.val.compute n).lo (y.val.compute n).hi).hi at ho
  change (ComplexCompute.ofRealCompute (RealCompute.mul x.val y.val)).compute n |>.Overlaps _
  simpa [toComplex,mul,ComplexCompute.ofRealCompute,ComplexCompute.mul,RealCompute.mul,RealCompute.mulCompute,
    QBox.mul,QBox.mulRealInterval,QBox.Overlaps,QComplex.le_def,QComplex.add,QComplex.sub,
    QComplex.mul,QComplex.neg,min4,max4,minRat,maxRat2,Rat.sub_eq_add_neg,Rat.neg_zero,Rat.add_zero,Rat.zero_add,Rat.mul_zero,Rat.zero_mul] using And.intro (And.intro ho (Rat.le_refl (a:=0))) (And.intro ho (Rat.le_refl (a:=0)))

theorem add_comm (x y : Value) : x+y=y+x := by
  apply toComplex_injective
  simp only [toComplex_add]
  exact ComplexComputeQuotient.add_comm _ _

theorem add_assoc (x y z : Value) : (x+y)+z=x+(y+z) := by
  apply toComplex_injective
  simp only [toComplex_add]
  exact ComplexComputeQuotient.add_assoc _ _ _

@[simp] theorem add_zero (x : Value) : x+0=x := by
  apply toComplex_injective
  simp only [toComplex_add,toComplex_zero,ComplexComputeQuotient.add_zero]

@[simp] theorem zero_add (x : Value) : 0+x=x := by rw [add_comm,add_zero]

@[simp] theorem add_neg (x : Value) : x+ -x=0 := by
  apply toComplex_injective
  simp only [toComplex_add,toComplex_neg,toComplex_zero,ComplexComputeQuotient.add_neg]

theorem mul_comm (x y : Value) : x*y=y*x := by
  apply toComplex_injective
  simp only [toComplex_mul]
  exact ComplexComputeQuotient.mul_comm _ _

theorem mul_assoc (x y z : Value) : (x*y)*z=x*(y*z) := by
  apply toComplex_injective
  simp only [toComplex_mul]
  exact ComplexComputeQuotient.mul_assoc _ _ _

@[simp] theorem mul_one (x : Value) : x*1=x := by
  apply toComplex_injective
  simp only [toComplex_mul,toComplex_one,ComplexComputeQuotient.mul_one]

@[simp] theorem one_mul (x : Value) : 1*x=x := by rw [mul_comm,mul_one]

@[simp] theorem mul_zero (x : Value) : x*0=0 := by
  apply toComplex_injective
  simp only [toComplex_mul,toComplex_zero,ComplexComputeQuotient.mul_zero]

@[simp] theorem zero_mul (x : Value) : 0*x=0 := by rw [mul_comm,mul_zero]

theorem mul_add (x y z : Value) : x*(y+z)=x*y+x*z := by
  apply toComplex_injective
  simp only [toComplex_mul,toComplex_add]
  exact ComplexComputeQuotient.mul_add _ _ _

theorem add_mul (x y z : Value) : (x+y)*z=x*z+y*z := by
  rw [mul_comm,mul_add,mul_comm z x,mul_comm z y]

theorem neg_mul (x y : Value) : (-x)*y= -(x*y) := by
  apply toComplex_injective
  simp only [toComplex_mul,toComplex_neg]
  grind

theorem ofRat_add (a b : Rat) : ofRat (a+b)=ofRat a+ofRat b := by
  apply Quotient.sound
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  change (⟨a+b,a+b⟩ : QInterval).Overlaps ⟨a+b,a+b⟩
  exact ⟨Rat.le_refl,Rat.le_refl⟩

theorem ofRat_neg (a : Rat) : ofRat (-a)= -ofRat a := rfl

private def power (x : Value) : Nat → Value
  | 0 => 1
  | n+1 => power x n*x

instance : Lean.Grind.CommRing Value where
  natCast := ⟨fun n => ofRat (n : Rat)⟩
  ofNat := fun n => ⟨ofRat (n : Rat)⟩
  intCast := ⟨fun n => ofRat (n : Rat)⟩
  nsmul := ⟨fun n x => ofRat (n : Rat)*x⟩
  zsmul := ⟨fun n x => ofRat (n : Rat)*x⟩
  npow := ⟨power⟩
  sub := fun x y => x+ -y
  add_zero := add_zero
  add_comm := add_comm
  add_assoc := add_assoc
  mul_assoc := mul_assoc
  mul_one := mul_one
  one_mul := one_mul
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_comm := mul_comm
  neg_add_cancel := fun x => by rw [add_comm]; exact add_neg x
  sub_eq_add_neg := fun _ _ => rfl
  pow_zero := fun _ => rfl
  pow_succ := fun _ _ => rfl
  ofNat_succ := fun n => by
    change ofRat ((n+1 : Nat) : Rat)=ofRat (n : Rat)+ofRat 1
    rw [Rat.natCast_add,ofRat_add]
    rfl
  neg_zsmul := fun n x => by
    change ofRat ((-n : Int) : Rat)*x= -(ofRat (n : Rat)*x)
    rw [Rat.intCast_neg,ofRat_neg,neg_mul]
  zsmul_natCast_eq_nsmul := fun _ _ => rfl
  intCast_ofNat := fun _ => rfl
  intCast_neg := fun n => by
    change ofRat ((-n : Int) : Rat)= -ofRat (n : Rat)
    rw [Rat.intCast_neg,ofRat_neg]

theorem one_ne_zero : (1 : Value) ≠ 0 := by
  intro h
  have he : (RealCompute.ofRat 1).Equiv (RealCompute.ofRat 0) := equiv_of_ofRaw_eq h
  have hle := ((RealCompute.compareAt_overlap_iff _ _ 0 0).mp (he 0)).1
  change (1 : Rat) ≤ 0 at hle
  exact (by decide : ¬(1 : Rat)≤0) hle

/-- Totality is a mathematical proposition, not a real comparison algorithm. -/
theorem le_total (x y : Value) : x≤y ∨ y≤x := by
  refine Quotient.inductionOn₂ x y ?_
  intro x y
  change x.val.Le y.val ∨ y.val.Le x.val
  by_cases h : x.val.Le y.val
  · exact Or.inl h
  · apply Or.inr
    have hsep : ∃ n m,(y.val.compute m).hi < (x.val.compute n).lo := by
      classical
      exact Classical.byContradiction fun hn => h (fun n m => by
        have := fun hlt => hn ⟨n,m,hlt⟩
        grind)
    obtain ⟨n,m,hsep⟩ := hsep
    intro i j
    have hy := RealCompute.le_refl y.val y.property i m
    have hx := RealCompute.le_refl x.val x.property n j
    grind

theorem add_le_add {x y z w : Value} (hxy : x≤y) (hzw : z≤w) : x+z≤y+w := by
  revert hxy hzw
  refine Quotient.inductionOn₂ x y ?_
  intro x y
  refine Quotient.inductionOn₂ z w ?_
  intro z w hxy hzw n m
  have h1 := hxy n m
  have h2 := hzw n m
  change (x.val.compute n).lo+(z.val.compute n).lo≤(y.val.compute m).hi+(w.val.compute m).hi
  exact rat_add_le_add h1 h2

theorem add_le_add_right_iff (x y z : Value) : x+z≤y+z ↔ x≤y := by
  constructor
  · intro h
    have hc := add_le_add h (le_refl (-z))
    simpa only [add_assoc,add_neg,add_zero] using hc
  · intro h
    exact add_le_add h (le_refl z)

theorem sub_nonneg_iff (x y : Value) : 0≤y-x ↔ x≤y := by
  have hx : (0 : Value)+x=x := zero_add x
  have hy : (y-x)+x=y := by grind
  have h := add_le_add_right_iff 0 (y-x) x
  rw [hx,hy] at h
  exact h.symm

theorem mul_nonneg {x y : Value} (hx : 0≤x) (hy : 0≤y) : 0≤x*y := by
  revert hx hy
  refine Quotient.inductionOn₂ x y ?_
  intro x y hx hy n m
  have hxhi := hx 0 m
  have hyhi := hy 0 m
  change (0 : Rat)≤(x.val.compute m).hi at hxhi
  change (0 : Rat)≤(y.val.compute m).hi at hyhi
  have hp := QBox.mulRealInterval_contains
    (RealCompute.interval_order_of_valid x.val x.property m) (Rat.le_refl)
    (RealCompute.interval_order_of_valid y.val y.property m) (Rat.le_refl)
  exact Rat.le_trans (Rat.mul_nonneg hxhi hyhi) hp.2

theorem mul_le_mul_of_nonneg_left {x y z : Value} (hxy : x≤y) (hz : 0≤z) : z*x≤z*y := by
  have hd := mul_nonneg hz ((sub_nonneg_iff x y).mpr hxy)
  have he : z*(y-x)=z*y-z*x := by grind
  rw [he] at hd
  exact (sub_nonneg_iff _ _).mp hd

/-- Reciprocal on the genuine nonzero domain. Proof-only existence of a
separated interval justifies terminating search, rather than selecting data. -/
def reciprocal (x : Value) (hx : x≠0) : Value := by
  refine Quotient.pliftOn x (fun c hc => ?_) ?_
  · have hn : CertifiedReciprocal.Nonzero c.val := by
      intro hz
      apply hx
      exact hc.trans (ofRaw_eq_ofRaw hz)
    exact ofRaw (CertifiedReciprocal.reciprocal c.val hn)
      (CertifiedReciprocal.reciprocal_valid c.val c.property hn)
  · intro a b ha hb he
    apply ofRaw_eq_ofRaw
    exact CertifiedReciprocal.reciprocal_congr a.val b.val a.property b.property _ _ he

@[simp] theorem reciprocal_ofRaw (x : RealCompute) (hx : x.Valid)
    (hn : ofRaw x hx≠0) :
    reciprocal (ofRaw x hx) hn = ofRaw
      (CertifiedReciprocal.reciprocal x (fun hz => hn (ofRaw_eq_ofRaw hz)))
      (CertifiedReciprocal.reciprocal_valid x hx (fun hz => hn (ofRaw_eq_ofRaw hz))) := rfl

theorem mul_reciprocal (x : Value) (hx : x≠0) : x*reciprocal x hx=1 := by
  revert hx
  refine Quotient.inductionOn x ?_
  intro x hx
  apply ofRaw_eq_ofRaw
  exact CertifiedReciprocal.mul_reciprocal x.val x.property _

theorem reciprocal_mul (x : Value) (hx : x≠0) : reciprocal x hx*x=1 := by
  rw [mul_comm,mul_reciprocal]

theorem reciprocal_unique (x y : Value) (hx : x≠0) (hy : x*y=1) : y=reciprocal x hx := by
  have hr := mul_reciprocal x hx
  grind

def divide (x y : Value) (hy : y≠0) : Value := x*reciprocal y hy

theorem divide_mul (x y : Value) (hy : y≠0) : divide x y hy*y=x := by
  have hr := reciprocal_mul y hy
  dsimp [divide]
  grind

theorem mul_cancel_left (x y z : Value) (hx : x≠0) (h : x*y=x*z) : y=z := by
  have hr := reciprocal_mul x hx
  have he := congrArg (fun t => reciprocal x hx*t) h
  grind

end ComputableAnalysis.RealComputeQuotient


