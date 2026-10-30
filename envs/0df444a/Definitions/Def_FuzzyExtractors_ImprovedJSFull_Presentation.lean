-- Prove2me | Definitions.Def_FuzzyExtractors_ImprovedJSFull_Presentation
-- name    : FuzzyExtractors_ImprovedJSFull_Presentation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:34:27.419189+00:00
-- url     : https://prove2.me/theorems/653f0ebc-493e-4557-8e02-d3f4dc95ecaa
-- title:
--   Public polynomial-basis finite-field presentations and binary encodings
-- statement:
--   A public presentation of a finite field $F$ supplies a prime $p$, a positive integer $k$, and the $k+1$ prime-field coefficients of a monic irreducible degree-$k$ polynomial. It certifies a ring isomorphism between $F$ and its polynomial quotient and represents each field element by $k$ coefficients in $\mathrm{GF}(p)$, with their polynomial evaluation reconstructing the element. It also records $|F|=p^k$. These are representation properties, without any computational hypotheses.
--
--   Prime-field digits use fixed-width little-endian binary strings. Natural-number parameters use binary digits, and list fields are framed by unary payload lengths with a separating zero. The public descriptor includes $p,k$ and the modulus, rather than an enumeration of $F$. Input sets are lists, and sketch vectors have their usual coefficient order.
--
--   $$T\le C\bigl(1+s+t+\lceil\log_2 |F|\rceil\bigr)^d.$$
--
--   The same polynomial form also bounds the descriptor length when $s=t=0$. Compactness requires injective element encodings, their exact digit lengths, and at most twice the rounded field-size logarithm per element. These are obligations of the main theorem, not assumed efficiency fields. The module makes the source's finite-field computation convention explicit for every characteristic.
-- source:
--   Dodis, Ostrovsky, Reyzin and Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4 (1 Apr 2008), https://arxiv.org/abs/cs/0602007v4, §6.2 finite-field preamble and Construction 5, printed pp.20–21 / PDF pp.21–22; Theorem 6.1, printed p.22 / PDF p.23; polynomial-basis binary presentation is an encoding convention

import Mathlib
import Definitions.Def_FuzzyExtractors_ImprovedJSFull_Computation

namespace FuzzyExtractors.ImprovedJSFull

/-! Public polynomial-basis finite-field encodings. Construction 5,
arXiv:cs/0602007v4, printed pp.20–21 / PDF 21–22. Representation
certificates below contain no algorithmic or time-bound fields. -/

/-- A monic coefficient-list polynomial over the prime field. -/
noncomputable def modulusPolynomial (p k : ℕ) (a : Fin (k + 1) → Fin p) : Polynomial (ZMod p) :=
  ∑ i : Fin (k + 1), Polynomial.C ((a i : ℕ) : ZMod p) * Polynomial.X ^ i.val

/-- A public GF(p^k) presentation of an abstract finite field. The quotient
isomorphism and coordinate reconstruction certify the ordinary mathematical
representation, not an efficient realization of any operation. -/
structure Presentation (F : Type) [Field F] [Fintype F] where
  p : ℕ
  k : ℕ
  prime : p.Prime
  positiveDegree : 0 < k
  coefficients : Fin (k + 1) → Fin p
  monic : (modulusPolynomial p k coefficients).Monic
  degree : (modulusPolynomial p k coefficients).natDegree = k
  irreducible : Irreducible (modulusPolynomial p k coefficients)
  quotientIso : F ≃+* AdjoinRoot (modulusPolynomial p k coefficients)
  scalar : ZMod p →+* F
  generator : F
  root : (modulusPolynomial p k coefficients).eval₂ scalar generator = 0
  coordinates : F ≃ (Fin k → Fin p)
  reconstruct : ∀ x : F,
    x = ∑ i : Fin k, scalar (coordinates x i : ℕ) * generator ^ i.val
  cardinality : Fintype.card F = p ^ k

/-- Fixed-width little-endian binary digits; no unary encoding of p or n. -/
def fixedBits (width value : ℕ) : Bits :=
  List.ofFn fun i : Fin width => value.testBit i.val

def natBits (value : ℕ) : Bits := fixedBits (Nat.clog 2 (value + 1)) value

/-- Unary lengths frame binary payloads; overhead is linear in payload size. -/
def pack (fields : List Bits) : Bits :=
  fields.flatMap fun w => List.replicate w.length true ++ [false] ++ w

/-- Uniform polynomial measured in the source parameters. -/
def timeBound (C : ℝ) (d s t bits : ℕ) : ENNReal :=
  ENNReal.ofReal (C * (1 + (s : ℝ) + (t : ℝ) + (bits : ℝ)) ^ d)

namespace Presentation

variable {F : Type} [Field F] [Fintype F] (P : Presentation F)

def digitWidth : ℕ := Nat.clog 2 P.p

def encodeElement (x : F) : Bits :=
  (List.ofFn (P.coordinates x)).flatMap fun digit => fixedBits P.digitWidth digit.val

/-- The public field descriptor has k+1 prime-field digits, not n entries. -/
def encode : Bits :=
  pack [natBits P.p, natBits P.k,
    (List.ofFn P.coefficients).flatMap fun digit => fixedBits P.digitWidth digit.val]

def encodeList (xs : List F) : Bits := xs.flatMap P.encodeElement

def encodeSketch {t : ℕ} (a : Fin t → F) : Bits := P.encodeList (List.ofFn a)

def sketchInput (s t : ℕ) (xs : List F) : Bits :=
  pack [P.encode, natBits s, natBits t, P.encodeList xs]

def recoveryInput (s t : ℕ) (xs : List F) (a : Fin t → F) : Bits :=
  pack [P.encode, natBits s, natBits t, P.encodeList xs, P.encodeSketch a]

/-- ceil(log₂ |F|), with |F|≥2 for every instance. -/
def universeBits : ℕ := Nat.clog 2 (P.p ^ P.k)

/-- A concrete representation-size assertion, to be established in the goal. -/
def Compact (C : ℝ) (d : ℕ) : Prop :=
  Function.Injective P.encodeElement ∧
  (∀ x, (P.encodeElement x).length = P.k * P.digitWidth) ∧
  P.k * P.digitWidth ≤ 2 * P.universeBits ∧
  (P.encode.length : ENNReal) ≤ timeBound C d 0 0 P.universeBits

end Presentation

end FuzzyExtractors.ImprovedJSFull


