-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealComputeQuotient
-- name    : liuyao_ca_fd889115_k1_Analysis_RealComputeQuotient
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:55:23.322278+00:00
-- url     : https://prove2.me/theorems/910e6146-95b8-44b6-8799-ca0176f68717
-- title:
--   Computable analysis · RealComputeQuotient · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RealComputeQuotient.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexComputeQuotientRing
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealMultiplication

set_option autoImplicit true

/-! Real values are equivalence classes of valid interval names.
The quotient forgets the choice of computation, not the interval construction
or its validity obligations. Executable algorithms remain at the raw layer. -/
namespace ComputableAnalysis.RealComputeQuotient

abbrev Certified := {x : RealCompute // x.Valid}

private def certifiedSetoid : Setoid Certified where
  r x y := x.val.Equiv y.val
  iseqv := ⟨fun x => RealCompute.equiv_refl x.val x.property,
    RealCompute.equiv_symm,
    fun {x y z} h k => RealCompute.equiv_trans x.property y.property z.property h k⟩

/-- The real numbers, formed from the existing valid interval names. -/
def Value := Quotient certifiedSetoid

def ofRaw (x : RealCompute) (hx : x.Valid) : Value :=
  Quotient.mk certifiedSetoid ⟨x,hx⟩

def ofRat (q : Rat) : Value := ofRaw (RealCompute.ofRat q) (RealCompute.ofRat_valid q)

theorem ofRaw_eq_ofRaw {x y : RealCompute} {hx : x.Valid} {hy : y.Valid}
    (h : x.Equiv y) : ofRaw x hx = ofRaw y hy := Quotient.sound h

theorem equiv_of_ofRaw_eq {x y : RealCompute} {hx : x.Valid} {hy : y.Valid}
    (h : ofRaw x hx = ofRaw y hy) : x.Equiv y := Quotient.exact h

theorem ofRaw_eq_iff {x y : RealCompute} {hx : x.Valid} {hy : y.Valid} :
    ofRaw x hx = ofRaw y hy ↔ x.Equiv y :=
  ⟨equiv_of_ofRaw_eq,ofRaw_eq_ofRaw⟩

/-- A legacy computation bundle denotes a value, independently of its metadata. -/
def ofComputation (x : ComputableAnalysis.RealCompute.Certified) : Value := ofRaw x.preferred x.valid

def add (x y : Value) : Value := Quotient.liftOn₂ x y
  (fun x y => ofRaw (x.val+y.val) (RealCompute.add_valid x.property y.property))
  (by
    intro x y x' y' hx hy
    exact Quotient.sound (RealCompute.add_equiv x.property x'.property y.property y'.property hx hy))

def neg (x : Value) : Value := Quotient.liftOn x
  (fun x => ofRaw (-x.val) (RealCompute.neg_valid x.property))
  (by intro x y h; exact Quotient.sound (RealCompute.neg_equiv h))

def mul (x y : Value) : Value := Quotient.liftOn₂ x y
  (fun x y => ofRaw (x.val*y.val) (RealCompute.mul_valid x.property y.property))
  (by
    intro x y x' y' hx hy
    exact Quotient.sound (RealCompute.mul_equiv x.property x'.property y.property y'.property hx hy))

instance : Zero Value := ⟨ofRat 0⟩
instance : One Value := ⟨ofRat 1⟩
instance : Add Value := ⟨add⟩
instance : Neg Value := ⟨neg⟩
instance : Sub Value := ⟨fun x y => add x (neg y)⟩
instance : Mul Value := ⟨mul⟩

private theorem raw_le_congr {x y a b : Certified}
    (hx : x.val.Equiv a.val) (hy : y.val.Equiv b.val) :
    x.val.Le y.val ↔ a.val.Le b.val := by
  constructor
  · intro h
    exact RealCompute.le_trans y.property
      (RealCompute.le_trans x.property
        (RealCompute.le_of_equiv a.property x.property (RealCompute.equiv_symm hx)) h)
      (RealCompute.le_of_equiv y.property b.property hy)
  · intro h
    exact RealCompute.le_trans b.property
      (RealCompute.le_trans a.property (RealCompute.le_of_equiv x.property a.property hx) h)
      (RealCompute.le_of_equiv b.property y.property (RealCompute.equiv_symm hy))

def le (x y : Value) : Prop := Quotient.liftOn₂ x y
  (fun x y => x.val.Le y.val)
  (by intro x y a b hx hy; exact propext (raw_le_congr hx hy))

instance : LE Value := ⟨le⟩

@[simp] theorem ofRaw_le_iff (x y : RealCompute) (hx : x.Valid) (hy : y.Valid) :
    ofRaw x hx ≤ ofRaw y hy ↔ x.Le y := Iff.rfl

theorem le_refl (x : Value) : x ≤ x := by
  refine Quotient.inductionOn x ?_
  intro x
  exact RealCompute.le_refl x.val x.property

theorem le_trans {x y z : Value} (h : x≤y) (k : y≤z) : x≤z := by
  revert h k
  refine Quotient.inductionOn₃ x y z ?_
  intro x y z h k
  exact RealCompute.le_trans y.property h k

theorem le_antisymm {x y : Value} (h : x≤y) (k : y≤x) : x=y := by
  revert h k
  refine Quotient.inductionOn₂ x y ?_
  intro x y h k
  exact Quotient.sound (RealCompute.le_antisymm h k)

/-- Inclusion of real values in the existing complex quotient. -/
def toComplex (x : Value) : ComplexComputeQuotient.Value := Quotient.liftOn x
  (fun x => ComplexComputeQuotient.ofRaw (ComplexCompute.ofRealCompute x.val)
    (ComplexCompute.ofRealCompute_valid x.val x.property))
  (by
    intro x y h
    exact ComplexComputeQuotient.ofRaw_eq_ofRaw
      (ComplexCompute.ofRealCompute_equiv_of_equiv x.property y.property h))

theorem toComplex_injective {x y : Value} (h : toComplex x = toComplex y) : x=y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro x y h
  have hc := ComplexCompute.realPart_equiv (ComplexComputeQuotient.equiv_of_ofRaw_eq h)
  exact Quotient.sound hc

end ComputableAnalysis.RealComputeQuotient


