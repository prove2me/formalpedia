-- Prove2me | Definitions.Def_IntegerRootsFN_Main_Binary
-- name    : IntegerRootsFN_Main_Binary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:43.127325+00:00
-- url     : https://prove2.me/theorems/c7a03ecd-51c5-47b1-81a3-02cf15b94aab
-- title:
--   Signed dense words and actual finite-machine execution
-- statement:
--   A word is a finite string over $\{0,1,\#\}$. Natural magnitudes use most-significant-bit-first binary, with zero's magnitude empty. Signed integers prepend one sign bit, and lists separate their signed entries with $\#$. Polynomial input starts with the binary header $n,b$ and contains all $n+1$ coefficients, each with a sign and exactly $b$ magnitude bits. Thus every valid polynomial is represented with order $nb$ input bits. Other finite records contain explicitly separated real and imaginary numerators, positive denominators, precision, list lengths or common exponents as appropriate.
--
--   For a published deterministic finite multitape machine $M$, a timed run is
--
--   $$\exists t\in\mathbb N:\quad t\le T\quad\text{and }M\text{ halts after }t\text{ actual transitions with the specified output word}.$$
--
--   The input tape is read-only, the other tapes begin blank, and halting fixes the output. The soft bound is $CF(1+\log_2(n+1))^k(1+\log_2(b+1))^l$. Theorems quantify the program, positive $C$, and fixed natural $k,l$ before all inputs. A root run requires an actual halting run emitting a complete, repetition-free signed integer-root list. These predicates do not assign a cost to an abstract arithmetic primitive.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 2, standing binary bit-operation model; p. 7, §3.1

import Mathlib
import Definitions.Def_IntMul_MultitapeWords
import Definitions.Def_IntegerRootsFN_Main_PolynomialData

set_option autoImplicit false

namespace IntegerRootsFN.Main

abbrev Word := List (Option Bool)

/-- Minimal magnitude bits, MSB first; zero has an empty magnitude. -/
def naturalWord (n : ℕ) : Word := IntMul.bits (IntMul.bin (Nat.clog 2 (n + 1)) n)

/-- One sign bit (true means negative) followed by magnitude bits. -/
def integerWord (z : ℤ) : Word :=
  some (decide (z < 0)) :: naturalWord z.natAbs

def integersWord (zs : List ℤ) : Word := IntMul.joinSep (zs.map integerWord)

/-- Header n,b followed by n+1 signed dense coefficients; each magnitude has b bits. -/
def polynomialWord (f : Polynomial ℤ) (n b : ℕ) : Word :=
  IntMul.joinSep ([naturalWord n, naturalWord b] ++
    List.ofFn fun j : Fin (n + 1) =>
      some (decide (f.coeff j.val < 0)) :: IntMul.bits (IntMul.bin b (f.coeff j.val).natAbs))

def gaussianWord (q : ℤ × ℤ) : Word :=
  IntMul.joinSep [integerWord q.1, integerWord q.2]

def gaussiansWord (qs : List (ℤ × ℤ)) : Word :=
  IntMul.joinSep (qs.map gaussianWord)

def rationalWord (z : GaussianRational) : Word :=
  IntMul.joinSep [integerWord z.re, integerWord z.im, naturalWord z.den]

def rationalsWord (zs : List GaussianRational) : Word :=
  IntMul.joinSep (zs.map rationalWord)

def panInputWord (P : ℕ) (a : DyadicPolynomial) : Word :=
  IntMul.joinSep [naturalWord (a.numerators.length - 1), naturalWord P,
    naturalWord a.exponent, gaussiansWord a.numerators]

def panOutputWord (B : ℕ) (ws : List (ℤ × ℤ)) : Word :=
  IntMul.joinSep [naturalWord B, gaussiansWord ws]

def evaluationWord (f : Polynomial ℤ) (n b : ℕ) (cs : List ℤ) : Word :=
  IntMul.joinSep [polynomialWord f n b, naturalWord cs.length, integersWord cs]

def testInputWord (f : Polynomial ℤ) (n b : ℕ) (m r : ℤ) : Word :=
  IntMul.joinSep [polynomialWord f n b, integerWord m, integerWord r]

/-- Actual deterministic transitions of the published finite machine; no assigned cost field. -/
def Runs (M : IntMul.MultitapeTM) (input output : Word) (T : ℝ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ M.HaltsWithOutputW input t output

/-- Positive shifted logarithms preserve all n,b≥1 edge inputs. -/
noncomputable def softBound (C : ℝ) (k l n b : ℕ) (F : ℝ) : ℝ :=
  C * F * (1 + logTwo ((n : ℝ) + 1)) ^ k * (1 + logTwo ((b : ℝ) + 1)) ^ l

/-- A single program and uniform constants are supplied by each theorem, outside this predicate. -/
def RootRuns (M : IntMul.MultitapeTM) (f : Polynomial ℤ) (n b : ℕ) (T : ℝ) : Prop :=
  ∃ rs : List ℤ, RootOutput f rs ∧ Runs M (polynomialWord f n b) (integersWord rs) T

end IntegerRootsFN.Main


