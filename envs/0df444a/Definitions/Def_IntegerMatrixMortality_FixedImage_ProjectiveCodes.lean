-- Prove2me | Definitions.Def_IntegerMatrixMortality_FixedImage_ProjectiveCodes
-- name    : IntegerMatrixMortality_FixedImage_ProjectiveCodes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:29:41.562255+00:00
-- url     : https://prove2.me/theorems/08779294-ab9c-407a-878d-a3484b42dc48
-- title:
--   Unary rational codes, valid points and guarded matrix factors
-- statement:
--   Fix a prime p≥7. The valid set V consists of rational points with reduced denominator prime to p; E is its complement in the full projective line and contains ∞. The residue of a reduced fraction a/b∈V is specified by a≡eb modulo p. Define
--
--   $$z_n=\frac{p^n}{1-p^{n+1}},\qquad X_{c,d}=\frac{p^c(1-p^{d+1})}{1-p^{c+d+2}}.$$
--
--   The factors are digit deletion Dₑ=(1 −e;0 p), auxiliary maps Mδ,h=(δ 0;ph 1), integer translations, and shifts Cq(z)=z+6q+1. The sign δ ranges over {−1,1}; before deletion it is +1. The six reserved local residues are Δ={−1,0,1,2,3,4}. All maps act on poles and infinity by their matrices.
--
--   These are actual rational and integer-matrix definitions. Rational-code formulas are used under the prime hypotheses that make their denominators nonzero.
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), §§5.1–5.2, PDF pp. 9–10 / printed pp. 7–8; (C.3), PDF p. 21 / printed p. 19

import Mathlib
import Definitions.Def_IntegerMatrixMortality_FixedImage_ProjectiveLine

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage
/-- Rational p-integral points. Infinity is excluded. -/
def Valid (p : ℕ) : ProjectivePoint → Prop
  | none => False
  | some z => ¬ (p : ℤ) ∣ (z.den : ℤ)

def Error (p : ℕ) (z : ProjectivePoint) : Prop := ¬ Valid p z

/-- Congruence on valid rational points by cleared denominators, without division in ZMod. -/
def HasResidue (p : ℕ) (z : ProjectivePoint) (e : ℤ) : Prop :=
  ∃ x : ℚ, z = some x ∧ Valid p z ∧ (p : ℤ) ∣ (x.num - e * (x.den : ℤ))

def InResidues (p : ℕ) (z : ProjectivePoint) (ds : Finset ℤ) : Prop :=
  ∃ d ∈ ds, HasResidue p z d

def delta : Finset ℤ := {-1,0,1,2,3,4}

def unaryCode (p n : ℕ) : ℚ := (p : ℚ)^n / (1 - (p : ℚ)^(n+1))
def intermediateCode (p c d : ℕ) : ℚ :=
  (p : ℚ)^c * (1 - (p : ℚ)^(d+1)) / (1 - (p : ℚ)^(c+d+2))

def deletionMatrix (p : ℕ) (e : ℤ) : ZMat := !![1,-e;0,(p : ℤ)]
def auxiliaryMatrix (p : ℕ) (neg : Bool) (h : ℤ) : ZMat :=
  !![if neg then -1 else 1,0;(p : ℤ)*h,1]
def translationMatrix (c : ℤ) : ZMat := !![1,c;0,1]
def shiftMatrix (q : ℕ) : ZMat := translationMatrix (6*(q : ℤ)+1)
def inverseShiftMatrix (q : ℕ) : ZMat := translationMatrix (-(6*(q : ℤ)+1))

def deleteDigit (p : ℕ) (e : ℤ) := projectiveAction (rationalMatrix (deletionMatrix p e))
def auxiliary (p : ℕ) (neg : Bool) (h : ℤ) :=
  projectiveAction (rationalMatrix (auxiliaryMatrix p neg h))
def translate (c : ℤ) := projectiveAction (rationalMatrix (translationMatrix c))
def shift (q : ℕ) := translate (6*(q : ℤ)+1)
def T (p : ℕ) := auxiliary p false (-1)
def Tinv (p : ℕ) := auxiliary p false 1

def encodedConfig (p q n : ℕ) : ProjectivePoint := shift q (some (unaryCode p n))

end IntegerMatrixMortality.FixedImage


