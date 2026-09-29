-- Prove2me | Definitions.Def_GeneralCK_E8_interval_checkers
-- name    : GeneralCK_E8_interval_checkers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T21:30:26.639608+00:00
-- url     : https://prove2.me/theorems/d44d9c61-bbcd-4984-87c2-81a52d55eb80
-- title:
--   Executable E8 dyadic logarithm, exponential, and stable graph checkers
-- statement:
--   At an arbitrary dyadic precision $p$, integer arithmetic computes outward enclosures for interval sums, products, reciprocals, and finite logarithm series. The logarithm checker validates rational power-of-two reduction witnesses, while the exponential checker compares checked logarithms of candidate endpoints. Order-five interval jet operations evaluate the stable E8 graph from four input intervals. DenominatorsPositive records the five required positive lower bounds. These are executable definitions; separate soundness theorems connect successful checks to real-valued enclosures. No numerical cell certificate or extra axiom is included.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/tree/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates

import Definitions.Def_GeneralCK_E8_semantic_core

open GeneralCK.Certificates.DyadicInterval
open GeneralCK.Certificates.E8TAxisStableInterval

namespace GeneralCK.Certificates



namespace DyadicInterval








def add {p : ℕ} (a b : DyadicInterval p) : DyadicInterval p := ⟨a.lo+b.lo, a.hi+b.hi⟩
def neg {p : ℕ} (a : DyadicInterval p) : DyadicInterval p := ⟨-a.hi, -a.lo⟩
def sub {p : ℕ} (a b : DyadicInterval p) : DyadicInterval p := a.add b.neg
def ofInt (p : ℕ) (z : ℤ) : DyadicInterval p := ⟨scale p*z, scale p*z⟩

def floorDiv (z d : ℤ) : ℤ := z/d
def ceilDiv (z d : ℤ) : ℤ := -((-z)/d)





def productLo {p : ℕ} (a b : DyadicInterval p) : ℤ :=
  min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))
def productHi {p : ℕ} (a b : DyadicInterval p) : ℤ :=
  max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))

def mul {p : ℕ} (a b : DyadicInterval p) : DyadicInterval p :=
  ⟨floorDiv (productLo a b) (scale p), ceilDiv (productHi a b) (scale p)⟩

/-- Sound only when the input lower endpoint is strictly positive. -/
def recip {p : ℕ} (a : DyadicInterval p) : DyadicInterval p :=
  ⟨floorDiv (scale p*scale p) a.hi, ceilDiv (scale p*scale p) a.lo⟩

















def subsetCheck {p : ℕ} (a b : DyadicInterval p) : Bool := decide (b.lo ≤ a.lo ∧ a.hi ≤ b.hi)
def positiveCheck {p : ℕ} (a : DyadicInterval p) : Bool := decide (0 < a.lo)













end DyadicInterval
end GeneralCK.Certificates

namespace GeneralCK.Certificates.DyadicLogSeries


/-- Partial sum and next odd power. Every executable endpoint is an integer. -/
def state {p : ℕ} (w : DyadicInterval p) : ℕ → DyadicInterval p × DyadicInterval p
  | 0 => (DyadicInterval.ofInt p 0,w)
  | n+1 =>
      let t := state w n
      (t.1.add (t.2.mul (DyadicInterval.ofInt p (2*(n:ℤ)+1)).recip),
       t.2.mul (w.mul w))

def denominator {p : ℕ} (w : DyadicInterval p) : DyadicInterval p :=
  (DyadicInterval.ofInt p 1).sub (w.mul w)

def partialSum {p : ℕ} (w : DyadicInterval p) (n : ℕ) : DyadicInterval p :=
  (DyadicInterval.ofInt p 2).mul (state w n).1

def remainder {p : ℕ} (w : DyadicInterval p) (n : ℕ) : DyadicInterval p :=
  ((DyadicInterval.ofInt p 2).mul (state w n).2).mul (denominator w).recip

def enclosure {p : ℕ} (w : DyadicInterval p) (n : ℕ) : DyadicInterval p :=
  ⟨(partialSum w n).lo, ((partialSum w n).add (remainder w n)).hi⟩

def guard {p : ℕ} (w : DyadicInterval p) : Bool :=
  decide (0 ≤ w.lo) && (denominator w).positiveCheck



























end GeneralCK.Certificates.DyadicLogSeries

namespace GeneralCK.Certificates.DyadicFastLog

def fraction (p : ℕ) (a b : ℤ) : DyadicInterval p :=
  ⟨DyadicInterval.floorDiv (DyadicInterval.scale p*a) b,
   DyadicInterval.ceilDiv (DyadicInterval.scale p*a) b⟩



/-- Reciprocal power-of-two reduction. Its validity is checked, not assumed. -/
def reduced (p : ℕ) (a b : ℤ) (e : ℕ) : DyadicInterval p :=
  fraction p (b-a*2^e) (b+a*2^e)

def approximation (p : ℕ) (a b : ℤ) (e n : ℕ) : DyadicInterval p :=
  (((DyadicInterval.ofInt p e).mul
    (DyadicLogSeries.enclosure (fraction p 1 3) n)).add
    (DyadicLogSeries.enclosure (reduced p a b e) n)).neg

def check {p : ℕ} (a b : ℤ) (e n : ℕ) (out : DyadicInterval p) : Bool :=
  decide (0<a ∧ 0<b) && DyadicLogSeries.guard (fraction p 1 3) &&
    DyadicLogSeries.guard (reduced p a b e) &&
    (approximation p a b e n).subsetCheck out



end GeneralCK.Certificates.DyadicFastLog

namespace GeneralCK.Certificates.DyadicExp



/-- The dyadic hull of two positive rational endpoint candidates. -/
def enclosure (p : ℕ) (lowerNum lowerDen upperNum upperDen : ℤ) :
    DyadicInterval p :=
  ⟨(DyadicFastLog.fraction p lowerNum lowerDen).lo,
   (DyadicFastLog.fraction p upperNum upperDen).hi⟩

/-- Check logs of the candidate endpoints and compare them with the input
interval. `logLower.hi ≤ input.lo` proves the lower candidate is below the
exponential; `input.hi ≤ logUpper.lo` proves the upper candidate is above it. -/
def check {p : ℕ} (input : DyadicInterval p)
    (lowerNum lowerDen upperNum upperDen : ℤ)
    (lowerExponent lowerTerms upperExponent upperTerms : ℕ)
    (logLower logUpper : DyadicInterval p) : Bool :=
  DyadicFastLog.check lowerNum lowerDen lowerExponent lowerTerms logLower &&
    DyadicFastLog.check upperNum upperDen upperExponent upperTerms logUpper &&
    decide (logLower.hi ≤ input.lo ∧ input.hi ≤ logUpper.lo)



end GeneralCK.Certificates.DyadicExp

namespace GeneralCK.Certificates

structure DyadicJet5Enclosure (p : ℕ) where
  d0 : DyadicInterval p
  d1 : DyadicInterval p
  d2 : DyadicInterval p
  d3 : DyadicInterval p
  d4 : DyadicInterval p
  d5 : DyadicInterval p
  deriving DecidableEq, Repr

namespace DyadicJet5Enclosure





def const (p : ℕ) (z : ℤ) : DyadicJet5Enclosure p :=
  ⟨ofInt p z, ofInt p 0, ofInt p 0, ofInt p 0, ofInt p 0, ofInt p 0⟩

def variableJet {p : ℕ} (i : DyadicInterval p) : DyadicJet5Enclosure p :=
  ⟨i, ofInt p 1, ofInt p 0, ofInt p 0, ofInt p 0, ofInt p 0⟩

def add {p : ℕ} (b c : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  ⟨b.d0.add c.d0, b.d1.add c.d1, b.d2.add c.d2,
    b.d3.add c.d3, b.d4.add c.d4, b.d5.add c.d5⟩















end DyadicJet5Enclosure
end GeneralCK.Certificates

namespace GeneralCK.Certificates
namespace DyadicJet5Enclosure



def inv {p : ℕ} (b : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  let r1 := b.d0.recip
  let r2 := r1.mul r1
  let r3 := r2.mul r1
  let r4 := r3.mul r1
  let r5 := r4.mul r1
  let r6 := r5.mul r1
  let c2 := ofInt p 2
  let c6 := ofInt p 6
  let c8 := ofInt p 8
  let c10 := ofInt p 10
  let c20 := ofInt p 20
  let c24 := ofInt p 24
  let c36 := ofInt p 36
  let c60 := ofInt p 60
  let c90 := ofInt p 90
  let c120 := ofInt p 120
  let c240 := ofInt p 240
  ⟨r1,
   b.d1.neg.mul r2,
   (c2.mul (b.d1.mul b.d1)).mul r3 |>.sub (b.d2.mul r2),
   ((c6.mul ((b.d1.mul b.d1).mul b.d1)).neg.mul r4).add
     ((c6.mul (b.d1.mul b.d2)).mul r3) |>.sub (b.d3.mul r2),
   (((c24.mul (((b.d1.mul b.d1).mul b.d1).mul b.d1)).mul r5).sub
     ((c36.mul ((b.d1.mul b.d1).mul b.d2)).mul r4)).add
     ((c6.mul (b.d2.mul b.d2)).mul r3) |>.add
     ((c8.mul (b.d1.mul b.d3)).mul r3) |>.sub (b.d4.mul r2),
   ((((((c120.mul ((((b.d1.mul b.d1).mul b.d1).mul b.d1).mul b.d1)).neg.mul r6).add
     ((c240.mul (((b.d1.mul b.d1).mul b.d1).mul b.d2)).mul r5)).sub
     ((c90.mul ((b.d1.mul b.d2).mul b.d2)).mul r4)).sub
     ((c60.mul ((b.d1.mul b.d1).mul b.d3)).mul r4)).add
     ((c20.mul (b.d2.mul b.d3)).mul r3)).add
     ((c10.mul (b.d1.mul b.d4)).mul r3) |>.sub (b.d5.mul r2)⟩



/-- Logarithm propagation with a separately checked enclosure for the value. -/
def log {p : ℕ} (b : DyadicJet5Enclosure p) (l : DyadicInterval p) :
    DyadicJet5Enclosure p :=
  let r := b.inv
  let c2 := ofInt p 2
  let c3 := ofInt p 3
  let c4 := ofInt p 4
  let c6 := ofInt p 6
  ⟨l, b.d1.mul r.d0,
   (b.d2.mul r.d0).add (b.d1.mul r.d1),
   ((b.d3.mul r.d0).add ((c2.mul b.d2).mul r.d1)).add (b.d1.mul r.d2),
   (((b.d4.mul r.d0).add ((c3.mul b.d3).mul r.d1)).add
     ((c3.mul b.d2).mul r.d2)).add (b.d1.mul r.d3),
   ((((b.d5.mul r.d0).add ((c4.mul b.d4).mul r.d1)).add
     ((c6.mul b.d3).mul r.d2)).add ((c4.mul b.d2).mul r.d3)).add
     (b.d1.mul r.d4)⟩



end DyadicJet5Enclosure
end GeneralCK.Certificates

namespace GeneralCK.Certificates
namespace DyadicJet5Enclosure



def mul {p : ℕ} (a b : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  let c2 := ofInt p 2
  let c3 := ofInt p 3
  let c4 := ofInt p 4
  let c5 := ofInt p 5
  let c6 := ofInt p 6
  let c10 := ofInt p 10
  ⟨a.d0.mul b.d0,
   (a.d1.mul b.d0).add (a.d0.mul b.d1),
   ((a.d2.mul b.d0).add ((c2.mul a.d1).mul b.d1)).add (a.d0.mul b.d2),
   (((a.d3.mul b.d0).add ((c3.mul a.d2).mul b.d1)).add
      ((c3.mul a.d1).mul b.d2)).add (a.d0.mul b.d3),
   ((((a.d4.mul b.d0).add ((c4.mul a.d3).mul b.d1)).add
      ((c6.mul a.d2).mul b.d2)).add ((c4.mul a.d1).mul b.d3)).add
      (a.d0.mul b.d4),
   (((((a.d5.mul b.d0).add ((c5.mul a.d4).mul b.d1)).add
      ((c10.mul a.d3).mul b.d2)).add ((c10.mul a.d2).mul b.d3)).add
      ((c5.mul a.d1).mul b.d4)).add (a.d0.mul b.d5)⟩





end DyadicJet5Enclosure
end GeneralCK.Certificates

namespace GeneralCK.Certificates.E8TAxisStableInterval



def constant {p : ℕ} (v : DyadicInterval p) : DyadicJet5Enclosure p :=
  ⟨v, ofInt p 0, ofInt p 0, ofInt p 0, ofInt p 0, ofInt p 0⟩



def negative {p : ℕ} (v : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  ⟨v.d0.neg,v.d1.neg,v.d2.neg,v.d3.neg,v.d4.neg,v.d5.neg⟩





def zBox {p : ℕ} (i : Inputs p) : DyadicJet5Enclosure p :=
  let e := i.expNegTwo
  ⟨e, e.mul (ofInt p (-2)), e.mul (ofInt p 4), e.mul (ofInt p (-8)),
    e.mul (ofInt p 16), e.mul (ofInt p (-32))⟩



def onePlusZBox {p : ℕ} (i : Inputs p) := (DyadicJet5Enclosure.const p 1).add (zBox i)
def rBox {p : ℕ} (i : Inputs p) :=
  ((DyadicJet5Enclosure.const p 1).add (negative (zBox i))).mul (onePlusZBox i).inv
def qBox {p : ℕ} (i : Inputs p) :=
  ((DyadicJet5Enclosure.const p 4).mul (zBox i)).mul
    ((onePlusZBox i).mul (onePlusZBox i)).inv
def l1Box {p : ℕ} (i : Inputs p) := (onePlusZBox i).log i.logOnePlusExp
def ellBox {p : ℕ} (i : Inputs p) := (DyadicJet5Enclosure.variableJet i.alpha).add (l1Box i)
def hBox {p : ℕ} (i : Inputs p) :=
  (l1Box i).add ((((DyadicJet5Enclosure.const p 2).mul
    (DyadicJet5Enclosure.variableJet i.alpha)).mul (zBox i)).mul (onePlusZBox i).inv)

def yBox {p : ℕ} (i : Inputs p) :=
  ((DyadicJet5Enclosure.const p 2).mul (constant i.logTwo).inv).mul
    ((DyadicJet5Enclosure.variableJet i.alpha).add
      (((rBox i).mul (hBox i)).mul ((qBox i).mul (ellBox i)).inv))

/-- Every reciprocal in the evaluated graph has a checked positive denominator. -/
def DenominatorsPositive {p : ℕ} (i : Inputs p) : Prop :=
  0 < (onePlusZBox i).d0.lo ∧
  0 < ((onePlusZBox i).mul (onePlusZBox i)).d0.lo ∧
  0 < ((DyadicJet5Enclosure.const p 2).mul (hBox i)).d0.lo ∧
  0 < ((qBox i).mul (ellBox i)).d0.lo ∧ 0 < i.logTwo.lo





structure FastLogBoxWitness where
  lowerExponent : ℕ
  lowerTerms : ℕ
  upperExponent : ℕ
  upperTerms : ℕ

def logBoxCheck {p : ℕ} (input out : DyadicInterval p) (w : FastLogBoxWitness) : Bool :=
  decide (0 < input.lo) &&
    DyadicFastLog.check (scale p) input.lo w.lowerExponent w.lowerTerms out.neg &&
    DyadicFastLog.check (scale p) input.hi w.upperExponent w.upperTerms out.neg



structure ExpWitness (p : ℕ) where
  lowerNum : ℤ
  lowerDen : ℤ
  upperNum : ℤ
  upperDen : ℤ
  lowerExponent : ℕ
  lowerTerms : ℕ
  upperExponent : ℕ
  upperTerms : ℕ
  logLower : DyadicInterval p
  logUpper : DyadicInterval p

def expBoxCheck {p : ℕ} (input out : DyadicInterval p) (w : ExpWitness p) : Bool :=
  DyadicExp.check input w.lowerNum w.lowerDen w.upperNum w.upperDen
    w.lowerExponent w.lowerTerms w.upperExponent w.upperTerms w.logLower w.logUpper &&
  (DyadicExp.enclosure p w.lowerNum w.lowerDen w.upperNum w.upperDen).subsetCheck out








end GeneralCK.Certificates.E8TAxisStableInterval


