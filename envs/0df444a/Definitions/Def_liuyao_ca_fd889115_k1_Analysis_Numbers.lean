-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Numbers
-- name    : liuyao_ca_fd889115_k1_Analysis_Numbers
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:55:47.790297+00:00
-- url     : https://prove2.me/theorems/b472b3b5-923b-4ebc-bd7f-e25b8c2469eb
-- title:
--   Computable analysis · Numbers · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/Numbers.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealComputeQuotient

set_option autoImplicit true

/-! Public mathematical values, distinct from particular numerical computations.
Both types quotient already valid rational-interval/box names; neither imports
an external completion or selects a preferred executable representative. -/
namespace ComputableAnalysis

abbrev Real := RealComputeQuotient.Value
abbrev Complex := ComplexComputeQuotient.Value

namespace Real

/-- The quotient value of a valid raw interval computation. -/
def ofRaw (x : RealCompute) (hx : x.Valid) : ComputableAnalysis.Real :=
  RealComputeQuotient.ofRaw x hx

theorem ofRaw_eq_iff {x y : RealCompute} {hx : x.Valid} {hy : y.Valid} :
    ofRaw x hx = ofRaw y hy ↔ x.Equiv y :=
  RealComputeQuotient.ofRaw_eq_iff

/-- The exact rational value inside the real quotient. -/
def ofRat (q : Rat) : ComputableAnalysis.Real :=
  RealComputeQuotient.ofRat q

/-- Rationality is a property of the quotient value, independent of its raw
interval representative. -/
def Rational (x : ComputableAnalysis.Real) : Prop :=
  Exists fun q : Rat => x = ofRat q

/-- Irrationality is the negation of rationality at the quotient-value layer. -/
def Irrational (x : ComputableAnalysis.Real) : Prop :=
  ¬ Rational x

namespace RationalPolynomial

abbrev Coefficients := List Rat

/-- At least one coefficient is nonzero. -/
def Nonzero (p : Coefficients) : Prop :=
  Exists fun n : Nat =>
    Exists fun c : Rat => p[n]? = some c /\ c ≠ 0

/-- Horner evaluation of a rational polynomial at a quotient real. -/
def eval (p : Coefficients) (x : ComputableAnalysis.Real) : ComputableAnalysis.Real :=
  p.foldr (fun c acc => RealComputeQuotient.add (ofRat c)
    (RealComputeQuotient.mul x acc)) (ofRat 0)

end RationalPolynomial

/-- Algebraicity over the rationals, stated directly for quotient values. -/
def Algebraic (x : ComputableAnalysis.Real) : Prop :=
  Exists fun p : RationalPolynomial.Coefficients =>
    RationalPolynomial.Nonzero p /\
      RationalPolynomial.eval p x = ofRat 0

/-- Transcendence over the rationals is the negation of algebraicity. -/
def Transcendental (x : ComputableAnalysis.Real) : Prop :=
  ¬ Algebraic x

theorem rational_ofRaw_iff (x : RealCompute) (hx : x.Valid) :
    Rational (ofRaw x hx) ↔ RealCompute.Rational x := by
  unfold Rational RealCompute.Rational
  constructor
  · rintro ⟨q, hxq⟩
    exact ⟨q, RealComputeQuotient.equiv_of_ofRaw_eq hxq⟩
  · rintro ⟨q, hxq⟩
    exact ⟨q, RealComputeQuotient.ofRaw_eq_ofRaw hxq⟩

theorem irrational_ofRaw_iff (x : RealCompute) (hx : x.Valid) :
    Irrational (ofRaw x hx) ↔ RealCompute.Irrational x := by
  unfold Irrational
  rw [rational_ofRaw_iff x hx]
  exact (RealCompute.irrational_iff_not_rational x).symm

theorem algebraic_ofRaw_congr {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    Algebraic (ofRaw x hx) ↔ Algebraic (ofRaw y hy) := by
  change Algebraic (RealComputeQuotient.ofRaw x hx) ↔
    Algebraic (RealComputeQuotient.ofRaw y hy)
  rw [RealComputeQuotient.ofRaw_eq_ofRaw hxy]

theorem transcendental_ofRaw_congr {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    Transcendental (ofRaw x hx) ↔ Transcendental (ofRaw y hy) := by
  change Transcendental (RealComputeQuotient.ofRaw x hx) ↔
    Transcendental (RealComputeQuotient.ofRaw y hy)
  rw [RealComputeQuotient.ofRaw_eq_ofRaw hxy]

/-- A certified computation and its quotient value have the same
irrationality predicate. -/
theorem irrational_legacy_iff (x : ComputableAnalysis.RealCompute.Certified) :
    x.Irrational ↔ Irrational (ofRaw x.preferred x.valid) := by
  rw [ComputableAnalysis.RealCompute.Certified.irrational_iff_preferred_irrational]
  exact (irrational_ofRaw_iff x.preferred x.valid).symm

theorem rational_legacy_iff (x : ComputableAnalysis.RealCompute.Certified) :
    x.Rational ↔ Rational (ofRaw x.preferred x.valid) := by
  rw [ComputableAnalysis.RealCompute.Certified.rational_iff_preferred_rational]
  exact (rational_ofRaw_iff x.preferred x.valid).symm

end Real

end ComputableAnalysis

namespace ComputableAnalysis.RealCompute

/-- Algebraicity of a raw name is defined through its canonical quotient
value. The validity proof records that the raw name denotes a real. -/
def Algebraic (x : RealCompute) (hx : x.Valid) : Prop :=
  ComputableAnalysis.Real.Algebraic (ComputableAnalysis.Real.ofRaw x hx)

/-- Transcendence of a raw name is defined through its canonical quotient
value. -/
def Transcendental (x : RealCompute) (hx : x.Valid) : Prop :=
  ComputableAnalysis.Real.Transcendental (ComputableAnalysis.Real.ofRaw x hx)

theorem algebraic_congr {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    Algebraic x hx ↔ Algebraic y hy :=
  ComputableAnalysis.Real.algebraic_ofRaw_congr hx hy hxy

theorem transcendental_congr {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    Transcendental x hx ↔ Transcendental y hy :=
  ComputableAnalysis.Real.transcendental_ofRaw_congr hx hy hxy

end RealCompute
end ComputableAnalysis

namespace ComputableAnalysis.Complex

/-- The quotient value of a valid rectangular computation. -/
def ofRaw (z : ComplexCompute) (hz : z.Valid) : ComputableAnalysis.Complex :=
  ComplexComputeQuotient.ofRaw z hz

theorem ofRaw_eq_iff {z w : ComplexCompute} {hz : z.Valid} {hw : w.Valid} :
    ofRaw z hz = ofRaw w hw ↔ z.Equiv w :=
  ⟨ComplexComputeQuotient.equiv_of_ofRaw_eq, ComplexComputeQuotient.ofRaw_eq_ofRaw⟩

/-- The exact value of a rational complex point. -/
def ofQComplex (z : QComplex) : ComputableAnalysis.Complex :=
  ComplexComputeQuotient.ofQComplex z

def ofReal : ComputableAnalysis.Real → ComputableAnalysis.Complex := RealComputeQuotient.toComplex

theorem ofReal_injective {x y : ComputableAnalysis.Real} (h : ofReal x = ofReal y) : x=y :=
  RealComputeQuotient.toComplex_injective h

end Complex
end ComputableAnalysis


