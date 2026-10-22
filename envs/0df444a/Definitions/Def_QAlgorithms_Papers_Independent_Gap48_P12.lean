-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12
-- name    : QAlgorithms_Papers_Independent_Gap48_P12
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T21:31:59.985476+00:00
-- url     : https://prove2.me/theorems/6bcf7f99-5656-4a1d-8b95-8da7f42dafd4
-- title:
--   Definitions for Representation of Quantum Circuits with Clifford and $π/8$ Gates
-- statement:
--   The objects the formalized statements of *Representation of Quantum Circuits with Clifford and $π/8$ Gates* (arXiv:0806.3834) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CircuitLetter`: PDF pp.3–4: source gate letters; in the R variant `h` denotes R.
--   - `CircuitWord`: PDF p.3, Definition 1: finite strings, with the empty string included.
--   - `rMatrix`: PDF p.6, Remark 1: R=P²H, with negative lower-left entry.
--   - `CircuitBasis`: PDF pp.4,6: the two source bases, with h interpreted as H or R.
--   - `gateMatrix`: PDF pp.4,6: exact interpretation of each source gate letter.
--   - `chronologicalInstructions`: PDF pp.3–4,6: adapt printed source words to the frozen evaluator's chronological alphabet. P becomes s; R=P²H becomes the chronological instructions H,S,S. No scalar-phase letter is introduced. Source word lengths and T-counts are still measured before this expansion.
--   - `wordTCount`: PDF p.8: the number of actual T symbols, with P a distinct letter.
--   - `IsCliffordWord`: PDF p.4: Clifford words use only the first basis letter and P.
--   - `cliffordSet`: PDF p.4, Definition 4: exact matrices of first-letter/P words, including phases.
--   - `Representatives`: PDF p.5, Definition 6: a fixed shortest representative for each exact Clifford matrix. No normalization or uniqueness assertion is a field. The values of `word` outside `cliffordSet B` are immaterial.
--   - `IsNormalWord`: PDF p.5, Definition 7: precisely the recursive source grammar, with one selected Clifford tail. The empty tail permits the one-letter word T.
--   - `atMostT`: PDF pp.5,8: matrices admitting a word with at most n T letters.
--   - `minimalT`: PDF p.8, Lemma 1: the zero layer is M₀; positive layers are differences. This follows the proof's explicit inclusion of n=0, avoiding truncated subtraction.
--   - `ctSet`: PDF p.7: C_T(C₁) is an image with both membership conditions; it is not the centralizer of T. The adjoint is T's exact inverse.
--   - `leftCoset`: PDF p.7: the left coset S C_T(C₁), as a set of exact matrices.
--   - `generatedCT`: PDF p.7: group closure of the three printed symbolic generators. The theorem identifies its carrier; unitarity is not assumed as a hypothesis.
--   - `ctGroup`: PDF p.7: group realization of the image-defined set. Its carrier equality with that set is part of the quotient theorem, rather than a free assumption.
--   - `scalarRoot`: PDF p.7, corrected scalar roots: denominator 4, not the printed 8.
--   - `scalarKernel`: PDF p.7, corrected K: generated as a normal subgroup without assuming that the printed set is closed. Its exact eight-element carrier is asserted below.
--   - `blochMatrix`: PDF p.10, Definition 8: real Pauli coefficients.
--   - `PauliStabilizes`: PDF p.10: stabilization means eigenvalue exactly +1.
--   - `StabilizerCoefficients`: PDF p.12, Eq.(15): integer coefficient order xa,xb,ya,yb,za,zb.
--   - `coefficientCoordinate`: PDF p.12: coordinate at the actual level ell, with denominator (√2)^ell.
--   - `parityPattern`: PDF p.12: T1,...,T9 in that order; true means odd, false means even.
--   - `HasParity`: PDF p.12: all six parities are specified, including the even coordinates.
--   - `InParityClass`: PDF pp.12–13: membership concerns the actual output state and the integer stabilizer representation at level wordTCount(w), not an unrelated tuple. The 0-based label k represents the source's T(k+1).
--   - `wordOfString`: Appendix pp.15–17: parse displayed H/P/T words; I is the empty word. All table literals below contain only H and P, with I written as "".
--   - `tablePair`: Appendix pp.15–17: input Clifford word and right Clifford tail.
--   - `appendixTable1`: PDF p.15, Table 1: all 64 printed pairs, interleaved by row across the two columns.
--   - `appendixTable2`: PDF p.16, Table 2: all 64 printed pairs, interleaved by row across the two columns.
--   - `appendixTable3`: PDF p.17, Table 3: all 64 printed pairs, interleaved by row across the two columns.
--   - `appendixTable`: Appendix: select Table 1, 2, or 3 with a 0-based finite index.
--   - `appendixPrefix`: Appendix: I, H, PH are the three left prefixes.
--   - `appendixRow`: Appendix: a total row accessor; only in-range indices are used in the theorem.
--   - `rewriteTable`: PDF p.7 and Appendix: the full 192-rule table (input, prefix, right tail).
--   - `rewriteLookup`: PDF p.7: a fixed finite table lookup by the input Clifford matrix. The empty fallback merely totalizes unreachable non-Clifford inputs; table completeness is asserted, not assumed.
--   - `NormalizerState`: PDF pp.7–8: reversed stack of committed S T blocks and a current Clifford tail.
--   - `normalizeStep`: PDF pp.7–8: one left-to-right input step. H/P multiply the Clifford tail; T invokes the concrete rewrite table. An internal I prefix merges TT into P and pops the preceding block; the remaining right tail is reselected. The attached cost charges one input read, each fixed finite-table lookup, and each stack edit. Fixed Clifford products and representative selection are finite-table lookups (the alphabet and the exact Clifford group are fixed).
--   - `normalizeRun`: PDF pp.7–8: the actual state/cost fold; no correctness property is an input.
--   - `materialize`: PDF pp.7–8: materialize the printed word from the reversed stack.
--   - `normalizeWord`: PDF pp.7–8: returned normal-form word of the prescribed procedure.
--   - `normalizationCost`: PDF p.8: includes writing every output letter, in addition to the fold cost.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, https://arxiv.org/abs/0806.3834v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

/-!
Statements from Matsumoto and Amano, arXiv:0806.3834v1.
All words are printed from output to input, and evaluation includes global phase.
Paper-local definitions supplement the frozen gate/state definitions.
The page-7 scalar typo is explicitly corrected below; independent moderation is pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

-- Use Mathlib types directly; no paper-local Mat or Vec declaration.
local notation "Mat" => Matrix Bool Bool ℂ
local notation "Vec" => EuclideanSpace ℂ Bool

/-- PDF pp.3–4: source gate letters; in the R variant `h` denotes R. -/
inductive CircuitLetter
  | h | p | t
  deriving DecidableEq, Repr

/-- PDF p.3, Definition 1: finite strings, with the empty string included. -/
abbrev CircuitWord := List CircuitLetter

/-- PDF p.6, Remark 1: R=P²H, with negative lower-left entry. -/
def rMatrix : Mat := phaseS ^ 2 * hadamard

/-- PDF pp.4,6: the two source bases, with h interpreted as H or R. -/
inductive CircuitBasis
  | hp | rp
  deriving DecidableEq, Repr

/-- PDF pp.4,6: exact interpretation of each source gate letter. -/
def gateMatrix (B : CircuitBasis) : CircuitLetter → Mat
  | .h => match B with
    | .hp => hadamard
    | .rp => rMatrix
  | .p => phaseS
  | .t => gateT

/-- PDF pp.3–4,6: adapt printed source words to the frozen evaluator's
chronological alphabet. P becomes s; R=P²H becomes the chronological
instructions H,S,S. No scalar-phase letter is introduced. Source word
lengths and T-counts are still measured before this expansion. -/
def chronologicalInstructions (B : CircuitBasis) (w : CircuitWord) :
    List QAlgorithms.Papers.Independent.Next46.P21.Letter :=
  w.reverse.flatMap fun g => match g with
    | .h => match B with
      | .hp => [.h]
      | .rp => [.h, .s, .s]
    | .p => [.s]
    | .t => [.t]

-- This notation calls the imported frozen evaluator; it declares no local evaluator.
local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.8: the number of actual T symbols, with P a distinct letter. -/
def wordTCount (w : CircuitWord) : ℕ := w.count .t

/-- PDF p.4: Clifford words use only the first basis letter and P. -/
def IsCliffordWord (w : CircuitWord) : Prop := CircuitLetter.t ∉ w

/-- PDF p.4, Definition 4: exact matrices of first-letter/P words, including phases. -/
def cliffordSet (B : CircuitBasis) : Set Mat :=
  {U | ∃ w : CircuitWord, IsCliffordWord w ∧ wordMatrix B w = U}

/-- PDF p.5, Definition 6: a fixed shortest representative for each exact
Clifford matrix. No normalization or uniqueness assertion is a field.
The values of `word` outside `cliffordSet B` are immaterial. -/
structure Representatives (B : CircuitBasis) where
  word : Mat → CircuitWord
  clifford : ∀ U ∈ cliffordSet B, IsCliffordWord (word U)
  computes : ∀ U ∈ cliffordSet B, wordMatrix B (word U) = U
  shortest : ∀ U ∈ cliffordSet B, ∀ w : CircuitWord,
    IsCliffordWord w → wordMatrix B w = U → (word U).length ≤ w.length

/-- PDF p.5, Definition 7: precisely the recursive source grammar, with
one selected Clifford tail. The empty tail permits the one-letter word T. -/
inductive IsNormalWord (B : CircuitBasis) (reps : Representatives B) : CircuitWord → Prop
  | tail (U : Mat) (hU : U ∈ cliffordSet B) : IsNormalWord B reps (reps.word U)
  | withT (w : CircuitWord) (hw : IsNormalWord B reps w) (hhead : w.head? ≠ some .t) :
      IsNormalWord B reps (.t :: w)
  | withHT (w : CircuitWord) (hw : IsNormalWord B reps w) (hhead : w.head? ≠ some .t) :
      IsNormalWord B reps (.h :: .t :: w)
  | withPHT (w : CircuitWord) (hw : IsNormalWord B reps w) (hhead : w.head? ≠ some .t) :
      IsNormalWord B reps (.p :: .h :: .t :: w)

/-- PDF pp.5,8: matrices admitting a word with at most n T letters. -/
def atMostT (n : ℕ) : Set Mat :=
  {U | ∃ w : CircuitWord, wordTCount w ≤ n ∧ wordMatrix .hp w = U}

/-- PDF p.8, Lemma 1: the zero layer is M₀; positive layers are differences.
This follows the proof's explicit inclusion of n=0, avoiding truncated subtraction. -/
def minimalT : ℕ → Set Mat
  | 0 => atMostT 0
  | n + 1 => atMostT (n + 1) \ atMostT n

/-- PDF p.7: C_T(C₁) is an image with both membership conditions;
it is not the centralizer of T. The adjoint is T's exact inverse. -/
def ctSet : Set Mat :=
  {U | ∃ g : Mat, g ∈ cliffordSet .hp ∧
    gateT * g * star gateT ∈ cliffordSet .hp ∧ U = gateT * g * star gateT}

/-- PDF p.7: the left coset S C_T(C₁), as a set of exact matrices. -/
def leftCoset (S : Mat) : Set Mat := (fun U => S * U) '' ctSet

/-- PDF p.7: group closure of the three printed symbolic generators.
The theorem identifies its carrier; unitarity is not assumed as a hypothesis. -/
def generatedCT : Subgroup (Matrix.unitaryGroup Bool ℂ) :=
  Subgroup.closure {u | (u : Mat) = phaseS ∨
    (u : Mat) = hadamard * phaseS ^ 2 * hadamard ∨
    (u : Mat) = (hadamard * phaseS ^ 3) ^ 3}

/-- PDF p.7: group realization of the image-defined set. Its carrier equality
with that set is part of the quotient theorem, rather than a free assumption. -/
def ctGroup : Subgroup (Matrix.unitaryGroup Bool ℂ) :=
  Subgroup.closure {u : Matrix.unitaryGroup Bool ℂ | (u : Mat) ∈ ctSet}

/-- PDF p.7, corrected scalar roots: denominator 4, not the printed 8. -/
def scalarRoot (k : Fin 8) : Mat :=
  Complex.exp (Complex.I * Real.pi * (k.val : ℂ) / 4) • (1 : Mat)

/-- PDF p.7, corrected K: generated as a normal subgroup without assuming
that the printed set is closed. Its exact eight-element carrier is asserted below. -/
def scalarKernel : Subgroup ctGroup :=
  Subgroup.normalClosure {g | ∃ k : Fin 8,
    (((g : ctGroup) : Matrix.unitaryGroup Bool ℂ) : Mat) = scalarRoot k}

/-- The constructed kernel is normal by construction, without a free normality premise. -/
instance scalarKernelNormal : scalarKernel.Normal := by
  unfold scalarKernel
  infer_instance

/-- PDF p.10, Definition 8: real Pauli coefficients. -/
def blochMatrix (x y z : ℝ) : Mat :=
  (x : ℂ) • pauliX + (y : ℂ) • pauliY + (z : ℂ) • pauliZ

/-- PDF p.10: stabilization means eigenvalue exactly +1. -/
def PauliStabilizes (x y z : ℝ) (psi : Vec) : Prop :=
  act (blochMatrix x y z) psi = psi

/-- PDF p.12, Eq.(15): integer coefficient order xa,xb,ya,yb,za,zb. -/
abbrev StabilizerCoefficients := Fin 6 → ℤ

/-- PDF p.12: coordinate at the actual level ell, with denominator (√2)^ell. -/
def coefficientCoordinate (ell : ℕ) (q : StabilizerCoefficients) (j : Fin 3) : ℝ :=
  ((q ⟨2 * j.val, by omega⟩ : ℝ) +
    (q ⟨2 * j.val + 1, by omega⟩ : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ ell

/-- PDF p.12: T1,...,T9 in that order; true means odd, false means even. -/
def parityPattern (k : Fin 9) : Fin 6 → Bool :=
  (![![false, true, false, false, false, true],
     ![false, false, false, true, false, true],
     ![false, true, false, true, false, false],
     ![false, true, true, false, true, false],
     ![true, false, false, true, true, false],
     ![true, false, true, false, false, true],
     ![false, true, true, true, true, true],
     ![true, true, false, true, true, true],
     ![true, true, true, true, false, true]] : Fin 9 → Fin 6 → Bool) k

/-- PDF p.12: all six parities are specified, including the even coordinates. -/
def HasParity (k : Fin 9) (q : StabilizerCoefficients) : Prop :=
  ∀ j, if parityPattern k j then Odd (q j) else Even (q j)

/-- PDF pp.12–13: membership concerns the actual output state and the
integer stabilizer representation at level wordTCount(w), not an unrelated tuple.
The 0-based label k represents the source's T(k+1). -/
def InParityClass (k : Fin 9) (w : CircuitWord) : Prop :=
  ∃ q : StabilizerCoefficients, HasParity k q ∧
    PauliStabilizes (coefficientCoordinate (wordTCount w) q 0)
      (coefficientCoordinate (wordTCount w) q 1)
      (coefficientCoordinate (wordTCount w) q 2)
      (act (wordMatrix .hp w) (ket false))

/-- Appendix pp.15–17: parse displayed H/P/T words; I is the empty word.
All table literals below contain only H and P, with I written as "". -/
def wordOfString (s : String) : CircuitWord :=
  s.toList.filterMap fun c =>
    if c = 'H' then some .h else if c = 'P' then some .p
    else if c = 'T' then some .t else none

/-- Appendix pp.15–17: input Clifford word and right Clifford tail. -/
def tablePair (s t : String) : CircuitWord × CircuitWord := (wordOfString s, wordOfString t)

/-- PDF p.15, Table 1: all 64 printed pairs, interleaved by row across the two columns. -/
def appendixTable1 : List (CircuitWord × CircuitWord) :=
  [
    tablePair "" "",
    tablePair "PPHPPPHPHPPP" "PPHPPHPPP",
    tablePair "P" "P",
    tablePair "PPPHPPHPPP" "PPHPPPHPH",
    tablePair "PP" "PP",
    tablePair "HPHPPPHP" "PPPHPPHPP",
    tablePair "PPP" "PPP",
    tablePair "HPHPPHPHPP" "HPHPPHPHPP",
    tablePair "HPPPHPH" "HPPH",
    tablePair "HPPHPPP" "HPHPPPHPPP",
    tablePair "HPHPH" "HPHPH",
    tablePair "HPPHPPHPPH" "HPPHPPHPPH",
    tablePair "HPPPHPHP" "HPPHP",
    tablePair "PHPPHPP" "HPPPHPHPPP",
    tablePair "PHPPPHPH" "PHPPH",
    tablePair "HPPPHPPPHP" "HPPPHPPPHP",
    tablePair "HPHPHP" "HPHPHP",
    tablePair "PPHPPHP" "PHPPPHPHPP",
    tablePair "HPPPHPHPP" "HPPHPP",
    tablePair "PPPHPPH" "PPHPPPHPHP",
    tablePair "PHPPPHPHP" "PHPPHP",
    tablePair "HPHPPPHPP" "PPPHPPHPPP",
    tablePair "PPHPPPHPH" "PPHPPH",
    tablePair "HPHPPHPHPPP" "HPHPPHPHPPP",
    tablePair "HPHPHPP" "HPHPHPP",
    tablePair "HPHPPHPPHPH" "HPHPPHPPHPH",
    tablePair "HPPH" "HPHPPPH",
    tablePair "HPPHPPHPPHP" "HPPHPPHPPHP",
    tablePair "HPPPHPHPPP" "HPPHPPP",
    tablePair "HPPHPPPHPPH" "HPPHPPPHPPH",
    tablePair "PHPPHPPP" "HPPPHPH",
    tablePair "HPPPHPPPHPP" "HPPPHPPPHPP",
    tablePair "PHPPPHPHPP" "PHPPHPP",
    tablePair "PPHPPHPP" "PHPPPHPHPPP",
    tablePair "PPHPPPHPHP" "PPHPPHP",
    tablePair "PPPHPPHP" "PPHPPPHPHPP",
    tablePair "HPHPPPHPPP" "PPPHPPH",
    tablePair "HPHPPHPPHPHP" "HPHPPHPPHPHP",
    tablePair "HPHPHPPP" "HPHPHPPP",
    tablePair "HPPHPPHPPHPP" "HPPHPPHPPHPP",
    tablePair "HPHPPHPH" "HPHPPHPH",
    tablePair "HPPHPPPHPPHP" "HPPHPPPHPPHP",
    tablePair "HPPHP" "HPHPPPHP",
    tablePair "HPPPHPPPHPPP" "HPPPHPPPHPPP",
    tablePair "PHPPH" "HPPPHPHP",
    tablePair "PPPHPPHPP" "PPHPPPHPHPPP",
    tablePair "PHPPPHPHPPP" "PHPPHPPP",
    tablePair "HPHPPHPPHPHPP" "HPHPPHPPHPHPP",
    tablePair "PPHPPHPPP" "PHPPPHPH",
    tablePair "HPHPPPHPPHPPH" "HPHPPPHPPHPPH",
    tablePair "PPHPPPHPHPP" "PPHPPHPP",
    tablePair "HPPHPPHPPHPPP" "HPPHPPHPPHPPP",
    tablePair "HPHPPPH" "PPPHPPHP",
    tablePair "HPPHPPPHPPHPP" "HPPHPPPHPPHPP",
    tablePair "HPHPPHPHP" "HPHPPHPHP",
    tablePair "HPHPPHPPHPHPPP" "HPHPPHPPHPHPPP",
    tablePair "HPPHPP" "HPHPPPHPP",
    tablePair "HPHPPPHPPHPPHP" "HPHPPPHPPHPPHP",
    tablePair "PHPPHP" "HPPPHPHPP",
    tablePair "HPPHPPPHPPHPPP" "HPPHPPPHPPHPPP",
    tablePair "HPPPHPPPH" "HPPPHPPPH",
    tablePair "HPHPPPHPPHPPHPP" "HPHPPPHPPHPPHPP",
    tablePair "PPHPPH" "PHPPPHPHP",
    tablePair "HPHPPPHPPHPPHPPP" "HPHPPPHPPHPPHPPP"
  ]

/-- PDF p.16, Table 2: all 64 printed pairs, interleaved by row across the two columns. -/
def appendixTable2 : List (CircuitWord × CircuitWord) :=
  [
    tablePair "H" "",
    tablePair "HPPHPPPHPHPPP" "PPHPPHPPP",
    tablePair "HP" "P",
    tablePair "HPPPHPPHPPP" "PPHPPPHPH",
    tablePair "HPP" "PP",
    tablePair "PHPPPHP" "PPPHPPHPP",
    tablePair "HPPP" "PPP",
    tablePair "PHPPHPHPP" "HPHPPHPHPP",
    tablePair "PPPHPH" "HPPH",
    tablePair "PPHPPP" "HPHPPPHPPP",
    tablePair "PHPH" "HPHPH",
    tablePair "PPHPPHPPH" "HPPHPPHPPH",
    tablePair "PPPHPHP" "HPPHP",
    tablePair "HPHPPHPP" "HPPPHPHPPP",
    tablePair "HPHPPPHPH" "PHPPH",
    tablePair "PPPHPPPHP" "HPPPHPPPHP",
    tablePair "PHPHP" "HPHPHP",
    tablePair "HPPHPPHP" "PHPPPHPHPP",
    tablePair "PPPHPHPP" "HPPHPP",
    tablePair "HPPPHPPH" "PPHPPPHPHP",
    tablePair "HPHPPPHPHP" "PHPPHP",
    tablePair "PHPPPHPP" "PPPHPPHPPP",
    tablePair "HPPHPPPHPH" "PPHPPH",
    tablePair "PHPPHPHPPP" "HPHPPHPHPPP",
    tablePair "PHPHPP" "HPHPHPP",
    tablePair "PHPPHPPHPH" "HPHPPHPPHPH",
    tablePair "PPH" "HPHPPPH",
    tablePair "PPHPPHPPHP" "HPPHPPHPPHP",
    tablePair "PPPHPHPPP" "HPPHPPP",
    tablePair "PPHPPPHPPH" "HPPHPPPHPPH",
    tablePair "HPHPPHPPP" "HPPPHPH",
    tablePair "PPPHPPPHPP" "HPPPHPPPHPP",
    tablePair "HPHPPPHPHPP" "PHPPHPP",
    tablePair "HPPHPPHPP" "PHPPPHPHPPP",
    tablePair "HPPHPPPHPHP" "PPHPPHP",
    tablePair "HPPPHPPHP" "PPHPPPHPHPP",
    tablePair "PHPPPHPPP" "PPPHPPH",
    tablePair "PHPPHPPHPHP" "HPHPPHPPHPHP",
    tablePair "PHPHPPP" "HPHPHPPP",
    tablePair "PPHPPHPPHPP" "HPPHPPHPPHPP",
    tablePair "PHPPHPH" "HPHPPHPH",
    tablePair "PPHPPPHPPHP" "HPPHPPPHPPHP",
    tablePair "PPHP" "HPHPPPHP",
    tablePair "PPPHPPPHPPP" "HPPPHPPPHPPP",
    tablePair "HPHPPH" "HPPPHPHP",
    tablePair "HPPPHPPHPP" "PPHPPPHPHPPP",
    tablePair "HPHPPPHPHPPP" "PHPPHPPP",
    tablePair "PHPPHPPHPHPP" "HPHPPHPPHPHPP",
    tablePair "HPPHPPHPPP" "PHPPPHPH",
    tablePair "PHPPPHPPHPPH" "HPHPPPHPPHPPH",
    tablePair "HPPHPPPHPHPP" "PPHPPHPP",
    tablePair "PPHPPHPPHPPP" "HPPHPPHPPHPPP",
    tablePair "PHPPPH" "PPPHPPHP",
    tablePair "PPHPPPHPPHPP" "HPPHPPPHPPHPP",
    tablePair "PHPPHPHP" "HPHPPHPHP",
    tablePair "PHPPHPPHPHPPP" "HPHPPHPPHPHPPP",
    tablePair "PPHPP" "HPHPPPHPP",
    tablePair "PHPPPHPPHPPHP" "HPHPPPHPPHPPHP",
    tablePair "HPHPPHP" "HPPPHPHPP",
    tablePair "PPHPPPHPPHPPP" "HPPHPPPHPPHPPP",
    tablePair "PPPHPPPH" "HPPPHPPPH",
    tablePair "PHPPPHPPHPPHPP" "HPHPPPHPPHPPHPP",
    tablePair "HPPHPPH" "PHPPPHPHP",
    tablePair "PHPPPHPPHPPHPPP" "HPHPPPHPPHPPHPPP"
  ]

/-- PDF p.17, Table 3: all 64 printed pairs, interleaved by row across the two columns. -/
def appendixTable3 : List (CircuitWord × CircuitWord) :=
  [
    tablePair "PH" "",
    tablePair "HPPPHPPHPPHPPP" "PPHPPHPPP",
    tablePair "PHP" "P",
    tablePair "PHPPPHPPHPPP" "PPHPPPHPH",
    tablePair "PHPP" "PP",
    tablePair "PPHPPPHP" "PPPHPPHPP",
    tablePair "PHPPP" "PPP",
    tablePair "PPHPPHPHPP" "HPHPPHPHPP",
    tablePair "HPH" "HPPH",
    tablePair "PPPHPPP" "HPHPPPHPPP",
    tablePair "PPHPH" "HPHPH",
    tablePair "PPPHPPHPPH" "HPPHPPHPPH",
    tablePair "HPHP" "HPPHP",
    tablePair "HPPHPHPPP" "HPPPHPHPPP",
    tablePair "HPPHPPHPHP" "PHPPH",
    tablePair "HPPPHP" "HPPPHPPPHP",
    tablePair "PPHPHP" "HPHPHP",
    tablePair "PHPPHPPHP" "PHPPPHPHPP",
    tablePair "HPHPP" "HPPHPP",
    tablePair "PHPPPHPPH" "PPHPPPHPHP",
    tablePair "HPPHPPHPHPP" "PHPPHP",
    tablePair "PPHPPPHPP" "PPPHPPHPPP",
    tablePair "HPPPHPPHPPH" "PPHPPH",
    tablePair "PPHPPHPHPPP" "HPHPPHPHPPP",
    tablePair "PPHPHPP" "HPHPHPP",
    tablePair "HPHPPHPPHPP" "HPHPPHPPHPH",
    tablePair "PPPH" "HPHPPPH",
    tablePair "PPPHPPHPPHP" "HPPHPPHPPHP",
    tablePair "HPHPPP" "HPPHPPP",
    tablePair "HPPHPPPHPPP" "HPPHPPPHPPH",
    tablePair "HPPHPH" "HPPPHPH",
    tablePair "HPPPHPP" "HPPPHPPPHPP",
    tablePair "HPPHPPHPHPPP" "PHPPHPP",
    tablePair "PHPPHPPHPP" "PHPPPHPHPPP",
    tablePair "HPPPHPPHPPHP" "PPHPPHP",
    tablePair "PHPPPHPPHP" "PPHPPPHPHPP",
    tablePair "PPHPPPHPPP" "PPPHPPH",
    tablePair "HPHPPHPPHPPP" "HPHPPHPPHPHP",
    tablePair "PPHPHPPP" "HPHPHPPP",
    tablePair "PPPHPPHPPHPP" "HPPHPPHPPHPP",
    tablePair "PPHPPHPH" "HPHPPHPH",
    tablePair "HPPHPPPH" "HPPHPPPHPPHP",
    tablePair "PPPHP" "HPHPPPHP",
    tablePair "HPPPHPPP" "HPPPHPPPHPPP",
    tablePair "HPPHPHP" "HPPPHPHP",
    tablePair "PHPPPHPPHPP" "PPHPPPHPHPPP",
    tablePair "HPPHPPHPH" "PHPPHPPP",
    tablePair "HPHPPHPPH" "HPHPPHPPHPHPP",
    tablePair "PHPPHPPHPPP" "PHPPPHPH",
    tablePair "HPHPPPHPPHPPP" "HPHPPPHPPHPPH",
    tablePair "HPPPHPPHPPHPP" "PPHPPHPP",
    tablePair "PPPHPPHPPHPPP" "HPPHPPHPPHPPP",
    tablePair "PPHPPPH" "PPPHPPHP",
    tablePair "HPPHPPPHP" "HPPHPPPHPPHPP",
    tablePair "PPHPPHPHP" "HPHPPHPHP",
    tablePair "HPHPPHPPHP" "HPHPPHPPHPHPPP",
    tablePair "PPPHPP" "HPHPPPHPP",
    tablePair "HPHPPPHPPH" "HPHPPPHPPHPPHP",
    tablePair "HPPHPHPP" "HPPPHPHPP",
    tablePair "HPPHPPPHPP" "HPPHPPPHPPHPPP",
    tablePair "HPPPH" "HPPPHPPPH",
    tablePair "HPHPPPHPPHP" "HPHPPPHPPHPPHPP",
    tablePair "PHPPHPPH" "PHPPPHPHP",
    tablePair "HPHPPPHPPHPP" "HPHPPPHPPHPPHPPP"
  ]

/-- Appendix: select Table 1, 2, or 3 with a 0-based finite index. -/
def appendixTable (j : Fin 3) : List (CircuitWord × CircuitWord) :=
  (![appendixTable1, appendixTable2, appendixTable3] : Fin 3 → List (CircuitWord × CircuitWord)) j

/-- Appendix: I, H, PH are the three left prefixes. -/
def appendixPrefix (j : Fin 3) : CircuitWord :=
  (![( [] : CircuitWord), [.h], [.p, .h]] : Fin 3 → CircuitWord) j

/-- Appendix: a total row accessor; only in-range indices are used in the theorem. -/
def appendixRow (j : Fin 3) (i : Fin 64) : CircuitWord × CircuitWord :=
  (appendixTable j).getD i.val ([], [])

/-- PDF p.7 and Appendix: the full 192-rule table (input, prefix, right tail). -/
def rewriteTable : List (CircuitWord × CircuitWord × CircuitWord) :=
  (appendixTable1.map fun p => (p.1, [], p.2)) ++
  (appendixTable2.map fun p => (p.1, [.h], p.2)) ++
  (appendixTable3.map fun p => (p.1, [.p, .h], p.2))

/-- PDF p.7: a fixed finite table lookup by the input Clifford matrix.
The empty fallback merely totalizes unreachable non-Clifford inputs;
table completeness is asserted, not assumed. -/
def rewriteLookup (U : Mat) : CircuitWord × CircuitWord := by
  classical
  exact match rewriteTable.find? (fun row => decide (wordMatrix .hp row.1 = U)) with
    | some row => (row.2.1, row.2.2)
    | none => ([], [])

/-- PDF pp.7–8: reversed stack of committed S T blocks and a current Clifford tail. -/
abbrev NormalizerState := List CircuitWord × CircuitWord

/-- PDF pp.7–8: one left-to-right input step. H/P multiply the Clifford tail;
T invokes the concrete rewrite table. An internal I prefix merges TT into P
and pops the preceding block; the remaining right tail is reselected.
The attached cost charges one input read, each fixed finite-table lookup,
and each stack edit. Fixed Clifford products and representative selection
are finite-table lookups (the alphabet and the exact Clifford group are fixed). -/
def normalizeStep (reps : Representatives .hp) (st : NormalizerState)
    (g : CircuitLetter) : NormalizerState × ℕ :=
  match g with
  | .h => ((st.1, reps.word (wordMatrix .hp st.2 * hadamard)), 2)
  | .p => ((st.1, reps.word (wordMatrix .hp st.2 * phaseS)), 2)
  | .t =>
    let rule := rewriteLookup (wordMatrix .hp st.2)
    match rule.1, st.1 with
    | [], a :: rest =>
      ((rest, reps.word (wordMatrix .hp a * phaseS * wordMatrix .hp rule.2)), 5)
    | s, stack => ((s :: stack, reps.word (wordMatrix .hp rule.2)), 4)

/-- PDF pp.7–8: the actual state/cost fold; no correctness property is an input. -/
def normalizeRun (reps : Representatives .hp) (w : CircuitWord) : NormalizerState × ℕ :=
  w.foldl (fun acc g =>
    let step := normalizeStep reps acc.1 g
    (step.1, acc.2 + step.2)) (([], reps.word 1), 1)

/-- PDF pp.7–8: materialize the printed word from the reversed stack. -/
def materialize (st : NormalizerState) : CircuitWord :=
  st.1.reverse.flatMap (fun s => s ++ [.t]) ++ st.2

/-- PDF pp.7–8: returned normal-form word of the prescribed procedure. -/
def normalizeWord (reps : Representatives .hp) (w : CircuitWord) : CircuitWord :=
  materialize (normalizeRun reps w).1

/-- PDF p.8: includes writing every output letter, in addition to the fold cost. -/
def normalizationCost (reps : Representatives .hp) (w : CircuitWord) : ℕ :=
  (normalizeRun reps w).2 + 3 * (normalizeRun reps w).1.1.length +
    (normalizeWord reps w).length + 1

/-! Small sanity examples for the new definition substrate (not target proofs). -/

example (B : CircuitBasis) : (1 : Mat) ∈ cliffordSet B :=
  ⟨[], by simp [IsCliffordWord], rfl⟩

example : (1 : Matrix.unitaryGroup Bool ℂ) ∈ generatedCT := generatedCT.one_mem

example : (1 : ctGroup) ∈ scalarKernel := scalarKernel.one_mem

example : scalarRoot 0 = (1 : Mat) := by
  simp [scalarRoot]

example : blochMatrix 0 0 1 = pauliZ := by
  simp [blochMatrix]

example : leftCoset 1 = ctSet := by
  simp [leftCoset]

example (B : CircuitBasis) : wordMatrix B [] = 1 := rfl

example (B : CircuitBasis) : wordMatrix B [.h, .p] = gateMatrix B .h * phaseS := by
  cases B <;> simp [chronologicalInstructions,
    QAlgorithms.Papers.Independent.Next46.P21.wordMatrix,
    QAlgorithms.Papers.Independent.Next46.P21.letterMatrix,
    gateMatrix, rMatrix, pow_two, mul_assoc]

example : chronologicalInstructions .rp [.h] =
    [QAlgorithms.Papers.Independent.Next46.P21.Letter.h, .s, .s] := rfl

example : wordMatrix .rp [.h] = phaseS ^ 2 * hadamard := by
  simp [chronologicalInstructions,
    QAlgorithms.Papers.Independent.Next46.P21.wordMatrix,
    QAlgorithms.Papers.Independent.Next46.P21.letterMatrix, pow_two, mul_assoc]

example : wordTCount [.t, .p, .t] = 2 := rfl

example : minimalT 0 = atMostT 0 := rfl

example (n : ℕ) : minimalT (n + 1) = atMostT (n + 1) \ atMostT n := rfl

example (B : CircuitBasis) (reps : Representatives B) (U : Mat)
    (hU : U ∈ cliffordSet B) : IsNormalWord B reps (reps.word U) :=
  IsNormalWord.tail U hU

example : PauliStabilizes 0 0 0 (0 : Vec) := by
  simp [PauliStabilizes, blochMatrix, act]

example : parityPattern 0 1 = true ∧ parityPattern 0 5 = true ∧
    parityPattern 0 0 = false := by decide

example : wordOfString "I" = [] ∧ wordOfString "PHT" = [.p, .h, .t] := by decide

example : appendixTable1.length = 64 ∧ appendixTable2.length = 64 ∧
    appendixTable3.length = 64 := by decide

example : appendixRow 0 0 = ([], []) := rfl

example (reps : Representatives .hp) :
    normalizeRun reps [] = (([], reps.word 1), 1) := rfl

end QAlgorithms.Papers.Independent.Gap48.P12


