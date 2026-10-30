-- Prove2me | Definitions.Def_FBMSP_Hardness
-- name    : FBMSP_Hardness
-- status  : Definition
-- author  : @mikeh
-- created : 2026-10-30T04:52:24.145903+00:00
-- url     : https://prove2.me/theorems/d2c95336-04b3-4127-9610-1cc9f5584fd2
-- title:
--   Explicit binary pricing decision problem and polynomial-time hardness
-- statement:
--   This bundle gives an explicit binary encoding of rational finite pricing instances, including the number of price slots and revenue threshold. Valid data have distinct nonnegative predicted means with positive normalized masses and a common finite mean-zero error law. Purchase is inclusive at the posted price; seller prices may be arbitrary nonnegative reals. Realized valuations are not required to be nonnegative.
--
--   NP is defined by a polynomially bounded certificate and a finite Turing-machine verifier with polynomial transition count. Polynomial many-one reductions use the same actual machine model. The target language restricts the number of listed error atoms by fixed constants $Cn^d$. No arbitrary encoding convention or unspecified computational oracle is used to assert hardness.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Theorem 1, p.14; proof pp.39–42 (ec5–ec8).

import Mathlib
import Mathlib.Computability.TuringMachine.Computable

/-!
# A binary-input decision problem for FBMSP hardness

These definitions specify the computational content of Theorem 1 of
Cui and Hamilton, *Optimal Feature-Based Market Segmentation and Pricing*,
DOI 10.1287/opre.2022.0490.

The input distribution is finite and rational.  The seller may nevertheless
choose arbitrary nonnegative REAL prices.  The number of allowed prices is
part of the binary input, not a fixed constant.  A single common shock
distribution is used for all customer means, expressing independence.

NP and polynomial many-one reductions are defined using Mathlib's finite
TM2 machines and a polynomial bound on their actual transition count.
No arbitrary `Encodable` instance, unspecified computational oracle, or
unbounded-time computable reduction is used.
-/

namespace FBMSP

abbrev BinaryString := List Bool

abbrev BinaryLanguage := Set BinaryString

/-- A pair of binary strings with one explicit separator symbol.  Its length
is exactly `x.length + w.length + 1`. -/
def verifierPairEncoding (xw : BinaryString × BinaryString) : List (Option Bool) :=
  xw.1.map some ++ none :: xw.2.map some

/-- A Boolean decision is encoded by its single Boolean output symbol. -/
def verifierOutputEncoding (b : Bool) : List Bool := [b]

/-- Standard certificate definition of NP: a total polynomial-time TM2
verifier and a polynomial bound on the number of witness bits.  Verifier time
is measured in the length of the explicitly delimited input/witness pair. -/
def InNP (L : BinaryLanguage) : Prop :=
  ∃ (V : BinaryString × BinaryString → Bool) (p : Polynomial ℕ),
    Nonempty (Turing.TM2ComputableInPolyTime
      verifierPairEncoding verifierOutputEncoding V) ∧
    ∀ x : BinaryString,
      x ∈ L ↔ ∃ w : BinaryString, w.length ≤ p.eval x.length ∧ V (x, w) = true

/-- A many-one reduction computed by a finite TM2 machine in polynomially
many transitions, measured in the source string's bit length. -/
def PolyManyOneReduction (A B : BinaryLanguage) : Prop :=
  ∃ f : BinaryString → BinaryString,
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun x : BinaryString => x) (fun x : BinaryString => x) f) ∧
    ∀ x : BinaryString, x ∈ A ↔ f x ∈ B

/-- Every NP language polynomial-time many-one reduces to the target. -/
def NPHard (L : BinaryLanguage) : Prop :=
  ∀ A : BinaryLanguage, InNP A → PolyManyOneReduction A L

/-- A self-delimiting bitstring: `length` one-bits, one zero-bit, then the
payload.  The unary part encodes the BIT LENGTH, not the represented integer.
Consequently a natural number occupies O(log n) bits. -/
def marketEncodeBits (bs : BinaryString) : BinaryString :=
  List.replicate bs.length true ++ false :: bs

/-- Little-endian base-two digits with an explicit bit-length prefix. -/
def marketEncodeNat (n : ℕ) : BinaryString :=
  marketEncodeBits ((Nat.digits 2 n).map (fun d => decide (d = 1)))

/-- A sign bit followed by the self-delimiting binary absolute value. -/
def marketEncodeInt (z : ℤ) : BinaryString :=
  decide (z < 0) :: marketEncodeNat z.natAbs

/-- Canonical rational numerator and positive denominator, each using the
explicit integer/natural binary encoding above. -/
def marketEncodeRat (q : ℚ) : BinaryString :=
  marketEncodeInt q.num ++ marketEncodeNat q.den

/-- A binary element count followed by self-delimiting element encodings. -/
def marketEncodeList {α : Type} (enc : α → BinaryString) (xs : List α) : BinaryString :=
  marketEncodeNat xs.length ++ xs.flatMap enc

/-- Concrete finite rational input.  Validity conditions are kept separate
so malformed strings and malformed numerical inputs are rejected. -/
structure RationalMarketInput where
  means : List ℚ
  weights : List ℚ
  shocks : List ℚ
  shockWeights : List ℚ
  segments : ℕ
  threshold : ℚ

/-- Every field is encoded explicitly; no Cantor-pairing or arbitrary
type-level encoding can distort the input-size measure. -/
def encodeRationalMarket (I : RationalMarketInput) : BinaryString :=
  marketEncodeList marketEncodeRat I.means ++
  marketEncodeList marketEncodeRat I.weights ++
  marketEncodeList marketEncodeRat I.shocks ++
  marketEncodeList marketEncodeRat I.shockWeights ++
  marketEncodeNat I.segments ++ marketEncodeRat I.threshold

/-- The means form the actual finite support: they are distinct and all have
strictly positive probability.  Shock probabilities may be zero; the support
bound used below bounds the entire supplied shock list and hence its support.
No assumption that every realized valuation is nonnegative is imposed. -/
def ValidRationalMarket (I : RationalMarketInput) : Prop :=
  0 < I.means.length ∧
  I.means.Nodup ∧
  (∀ x ∈ I.means, 0 ≤ x) ∧
  I.weights.length = I.means.length ∧
  (∀ w ∈ I.weights, 0 < w) ∧
  I.weights.sum = 1 ∧
  0 < I.shocks.length ∧
  I.shockWeights.length = I.shocks.length ∧
  (∀ w ∈ I.shockWeights, 0 ≤ w) ∧
  I.shockWeights.sum = 1 ∧
  ((I.shocks.zip I.shockWeights).map (fun z => z.1 * z.2)).sum = 0 ∧
  1 ≤ I.segments

/-- Expected revenue from assigning each feature-mean atom to one of the
offered prices.  Purchase occurs at valuation greater than or equal to price.
Matching list lengths in `ValidRationalMarket` ensure the `getD` defaults are
never used for the masses in a valid instance. -/
noncomputable def rationalMarketRevenue (I : RationalMarketInput)
    (prices : Fin I.segments → ℝ)
    (assignment : Fin I.means.length → Fin I.segments) : ℝ := by
  classical
  exact ∑ i : Fin I.means.length,
    (I.weights.getD i.val 0 : ℝ) *
      ∑ j : Fin I.shocks.length,
        (I.shockWeights.getD j.val 0 : ℝ) *
          (if prices (assignment i) ≤ (I.means.get i : ℝ) + (I.shocks.get j : ℝ)
           then prices (assignment i) else 0)

/-- The exact threshold decision problem; prices range over all nonnegative
reals, and unused price slots are allowed. -/
def MeetsPricingThreshold (I : RationalMarketInput) : Prop :=
  ∃ (prices : Fin I.segments → ℝ)
      (assignment : Fin I.means.length → Fin I.segments),
    (∀ j, 0 ≤ prices j) ∧
      (I.threshold : ℝ) ≤ rationalMarketRevenue I prices assignment

/-- Canonical encodings of yes-instances whose noise representation has at
most `C * n^d` atoms, where `n` is the number of distinct customer means.
Strings not encoding such valid inputs are outside the language. -/
def pricingLanguageWithShockBound (C d : ℕ) : BinaryLanguage :=
  {bits | ∃ I : RationalMarketInput,
    encodeRationalMarket I = bits ∧
    ValidRationalMarket I ∧
    I.shocks.length ≤ C * I.means.length ^ d ∧
    MeetsPricingThreshold I}

end FBMSP


