-- Prove2me | Definitions.Def_ApproxCountRwPHP_Unprovability_APX
-- name    : ApproxCountRwPHP_Unprovability_APX
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:58:46.28438+00:00
-- url     : https://prove2.me/theorems/d369b700-07a2-4256-a42b-7dc5ad57302c
-- title:
--   The four counting axioms and the rwPHP sentence
-- statement:
--   For a valid circuit C and positive precisions represented by nonempty strings, write Pδ(C) for P applied to C and the all-ones string of length δ⁻¹. The four universally quantified axioms assert rational values in [0,1], exact boundary values for circuits with no input reads, precision consistency, and rightmost-bit local consistency:
--
--   $$|P_{\delta_1}(C)-P_{\delta_2}(C)|\le\delta_1+\delta_2+\beta,$$
--   $$\left|P_\delta(C)-\frac{P_\delta(\operatorname{Fix}_0 C)+P_\delta(\operatorname{Fix}_1 C)}2\right|\le2\delta+\beta.$$
--
--   All circuit, precision, and slack variables are universally quantified. Both relativized APX theories are their respective universal bases plus these four sentences. The retraction principle is the string sentence
--
--   $$\forall u\ \exists x\ (|x|=|u|\ \land\ (|f(x)|\ge |u|\ \lor\ g(f(x))\ne x)).$$
--
--   The zero-length case is included. No set of all true counting statements is substituted for these four axioms.
--
--   The numerical-domain helpers numeralTerm and numericLess require canonical shortest numeral encodings. The counting precision variables and the strings in rwPHP remain arbitrary strings.
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), §3.1–3.2, equation (3.2), printed p. 16, 18–19, PDF p. 18, 20–21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=18, 20–21

import Definitions.Def_ApproxCountRwPHP_Unprovability_Languages

namespace ApproxCountRwPHP.Unprovability

abbrev ArithTerm (S : Signature) (n : ℕ) := (LanguageOver S).Term (Empty ⊕ Fin n)
abbrev ArithFormula (S : Signature) (n : ℕ) := (LanguageOver S).BoundedFormula Empty n

def avar {S : Signature} {n : ℕ} (i : Fin n) : ArithTerm S n := .var (.inr i)

def native {S : Signature} {n k : ℕ} (o : Native S k)
    (args : Fin k → ArithTerm S n) : ArithTerm S n := .func (.oracle o) args

def primitive {S : Signature} {n k : ℕ} (o : Primitive k)
    (args : Fin k → ArithTerm S n) : ArithTerm S n := .func (.primitive o) args

def azero {S : Signature} {n : ℕ} : ArithTerm S n := primitive .empty Fin.elim0

def aone {S : Signature} {n : ℕ} : ArithTerm S n := primitive (.append true) ![azero]

def holds {S : Signature} {n : ℕ} (t : ArithTerm S n) : ArithFormula S n := t.bdEqual aone

/-- Numerical domains use canonical encodings, so `< N` has exactly N
elements in the standard structure, rather than infinitely many padded words. -/
def numeralTerm {S : Signature} {n : ℕ} (t : ArithTerm S n) : ArithFormula S n :=
  holds (primitive .isNumeral ![t])

def numericLess {S : Signature} {n : ℕ} (x y : ArithTerm S n) : ArithFormula S n :=
  numeralTerm x ⊓ numeralTerm y ⊓ holds (primitive .less ![x,y])

def nonzeroPrecision {S : Signature} {n : ℕ} (u : ArithTerm S n) : ArithFormula S n :=
  (primitive .length ![u]).bdEqual azero |>.not

def countTerm {S : Signature} {n : ℕ} (C u : ArithTerm S n) : ArithTerm S n :=
  native .count ![C, primitive .onesLength ![u] ]

def deltaTerm {S : Signature} {n : ℕ} (u : ArithTerm S n) : ArithTerm S n :=
  native .inverseLength ![u]

def radd {S : Signature} {n : ℕ} (x y : ArithTerm S n) : ArithTerm S n := native .rationalAdd ![x,y]
def rsub {S : Signature} {n : ℕ} (x y : ArithTerm S n) : ArithTerm S n := native .rationalSub ![x,y]
def rabs {S : Signature} {n : ℕ} (x : ArithTerm S n) : ArithTerm S n := native .rationalAbs ![x]
def rle {S : Signature} {n : ℕ} (x y : ArithTerm S n) : ArithFormula S n := holds (native .rationalLE ![x,y])

/-- Basic: for every circuit and every defined positive precision, Pδ is a
valid rational representation whose value lies in [0,1]. -/
def basicAxiom (S : Signature) : (LanguageOver S).Sentence :=
  let C : ArithTerm S 2 := avar 0
  let u : ArithTerm S 2 := avar 1
  let p := countTerm C u
  ((holds (native .isCircuit ![C]) ⊓ nonzeroPrecision u).imp
    (holds (native .isRational ![p]) ⊓ rle azero p ⊓ rle p aone)).alls

/-- Boundary includes oracle evaluation of circuits without input reads. -/
def boundaryAxiom (S : Signature) : (LanguageOver S).Sentence :=
  let C : ArithTerm S 2 := avar 0
  let u : ArithTerm S 2 := avar 1
  ((holds (native .isCircuit ![C]) ⊓ nonzeroPrecision u ⊓ holds (native .noInputs ![C])).imp
    (rle (countTerm C u) (native .circuitVal ![C]) ⊓ rle (native .circuitVal ![C]) (countTerm C u))).alls

/-- Precision consistency, with all three precision/slack variables. -/
def precisionAxiom (S : Signature) : (LanguageOver S).Sentence :=
  let C : ArithTerm S 4 := avar 0
  let u : ArithTerm S 4 := avar 1
  let v : ArithTerm S 4 := avar 2
  let w : ArithTerm S 4 := avar 3
  ((holds (native .isCircuit ![C]) ⊓ nonzeroPrecision u ⊓ nonzeroPrecision v ⊓ nonzeroPrecision w).imp
    (rle (rabs (rsub (countTerm C u) (countTerm C v)))
      (radd (radd (deltaTerm u) (deltaTerm v)) (deltaTerm w)))).alls

/-- Local consistency, rightmost-bit restrictions and arbitrary positive slack. -/
def localAxiom (S : Signature) : (LanguageOver S).Sentence :=
  let C : ArithTerm S 3 := avar 0
  let u : ArithTerm S 3 := avar 1
  let w : ArithTerm S 3 := avar 2
  let average := native .rationalHalf ![
    radd (countTerm (native (.fix false) ![C]) u) (countTerm (native (.fix true) ![C]) u)]
  ((holds (native .isCircuit ![C]) ⊓ nonzeroPrecision u ⊓ nonzeroPrecision w).imp
    (rle (rabs (rsub (countTerm C u) average))
      (radd (radd (deltaTerm u) (deltaTerm u)) (deltaTerm w)))).alls

def countingAxioms (S : Signature) : (LanguageOver S).Theory :=
  {basicAxiom S, boundaryAxiom S, precisionAxiom S, localAxiom S}

def APX1fg : LangFG.Theory := baseFG ∪ countingAxioms signatureFG

def APX1Lhat (S : Signature) : (LangLhat S).Theory :=
  baseLhat S ∪ countingAxioms (parameterizedSignature S)

/-- Equation (3.2), including the zero-length case. -/
def rwPHPfg : LangFG.Sentence :=
  let u : ArithTerm signatureFG 2 := avar 0
  let x : ArithTerm signatureFG 2 := avar 1
  let fx := native (.query ⟨0, by decide⟩) ![x]
  let gfx := native (.query ⟨1, by decide⟩) ![fx]
  let lenx := primitive .length ![x]
  let lenu := primitive .length ![u]
  let lenfx := primitive .length ![fx]
  ((lenx.bdEqual lenu) ⊓ ((holds (primitive .less ![lenfx,lenu])).not ⊔ (gfx.bdEqual x).not)).ex.all

end ApproxCountRwPHP.Unprovability


