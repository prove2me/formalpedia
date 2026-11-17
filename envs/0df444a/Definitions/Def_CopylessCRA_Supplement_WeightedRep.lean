-- Prove2me | Definitions.Def_CopylessCRA_Supplement_WeightedRep
-- name    : CopylessCRA_Supplement_WeightedRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:57:46.631207+00:00
-- url     : https://prove2.me/theorems/c192c959-dd74-45b7-a22f-59cb7df427b6
-- title:
--   Binary-encoded rational weighted representations and exact Turing decision algorithms
-- statement:
--   A finite-alphabet rational weighted representation records the alphabet size, dimension, row vector $\lambda$, one rational matrix $M_a$ for each letter, and column vector $\gamma$. Its rational entries, dimensions and alphabet size have an explicit self-delimiting binary encoding.
--
--   The module defines intrinsic predicates saying that the represented series is invertible or unipotent, and a suite of five exact finite Turing-machine algorithms: minimization, invertibility testing, general invertible-sector CCRA membership, unipotence testing and unipotent-sector CCRA membership. The minimizer and the three polynomial-time decision procedures carry bounds by a natural polynomial in the binary input length; general invertible-sector membership carries only a termination-and-correctness certificate.
--
--   **Formalization Note** Rational numbers are encoded by their reduced signed numerator and positive denominator. Mathlib's finite multi-tape Turing-machine semantics counts actual machine steps, so rational arithmetic is not assigned unit cost.
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), Theorem 4, p.3 (PDF p.5); Appendix C.1–C.2, pp.16–17 (PDF pp.18–19)

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_CopylessCRA_CCRA
import Definitions.Def_CopylessCRA_IsRep
import Definitions.Def_CopylessCRA_Supplement_IsUnipotentSeries

open Matrix

namespace CopylessCRA
namespace Supplement

/-- A finite-alphabet rational weighted representation, the binary-encoded input object of
Theorem 4. -/
structure WeightedRep where
  alphabetSize : ℕ
  dim : ℕ
  lam : Fin dim -> ℚ
  M : Fin alphabetSize -> Matrix (Fin dim) (Fin dim) ℚ
  gamma : Fin dim -> ℚ

namespace WeightedRep

/-- The rational series computed by a weighted representation. -/
def series (E : WeightedRep) : List (Fin E.alphabetSize) -> ℚ :=
  fun w => E.lam ⬝ᵥ (wordMat E.M w *ᵥ E.gamma)

/-- Minimality of the represented weighted automaton. -/
def IsMinimal (E : WeightedRep) : Prop := IsMinimalRep E.lam E.M E.gamma

/-- Intrinsic invertibility of the series represented by `E`. -/
def IsInvertible (E : WeightedRep) : Prop := IsInvertibleSeries E.series

/-- Intrinsic unipotence of the series represented by `E`: some (equivalently every) minimal
representation has unipotent matrix for every word. -/
def IsUnipotent (E : WeightedRep) : Prop :=
  exists (d : ℕ) (lam : Fin d -> ℚ)
    (M : Fin E.alphabetSize -> Matrix (Fin d) (Fin d) ℚ) (gamma : Fin d -> ℚ),
      IsRep E.series lam M gamma ∧ IsMinimalRep lam M gamma ∧ IsUnipotentSeries M

/-- `E'` represents the same finite-alphabet series as `E`.  The equality of alphabet sizes is
part of the relation; the matrices of `E'` are transported along it. -/
def SameSeries (E E' : WeightedRep) : Prop :=
  exists h : E'.alphabetSize = E.alphabetSize, forall w : List (Fin E.alphabetSize),
    E.series w = E'.lam ⬝ᵥ
      (wordMat (fun a => E'.M (Fin.cast h.symm a)) w *ᵥ E'.gamma)

end WeightedRep

/-- A self-delimiting binary encoding of a natural number. -/
def encodeNat (n : ℕ) : List Bool :=
  let bits := Nat.bits n
  List.replicate bits.length true ++ false :: bits

/-- A binary encoding of an integer: a sign bit followed by the framed magnitude. -/
def encodeInt (z : ℤ) : List Bool := (z < 0) :: encodeNat z.natAbs

/-- Exact binary encoding of a reduced rational number by numerator and positive denominator. -/
def encodeRat (q : ℚ) : List Bool := encodeInt q.num ++ encodeNat q.den

/-- Binary encoding of a rational vector whose dimension is known from its surrounding object. -/
def encodeRatVector {n : ℕ} (v : Fin n -> ℚ) : List Bool :=
  (List.ofFn v).flatMap encodeRat

/-- Binary encoding of a square rational matrix whose dimension is known from its surrounding
object. -/
def encodeRatMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : List Bool :=
  (List.ofFn fun i => (List.ofFn fun j => A i j).flatMap encodeRat).flatten

/-- The binary input format for Theorem 4.  Dimensions and alphabet size are encoded first, then
the row vector, all letter matrices in alphabet order, and the column vector. -/
def encodeWeightedRep (E : WeightedRep) : List Bool :=
  encodeNat E.alphabetSize ++ encodeNat E.dim ++ encodeRatVector E.lam ++
    (List.ofFn fun a => encodeRatMatrix (E.M a)).flatten ++ encodeRatVector E.gamma

/-- The five uniform exact Turing algorithms asserted by Theorem 4.  The three algorithms carrying
a polynomial bound use Mathlib's finite multi-tape Turing-machine predicate with a polynomial in
the *bit length* of `encodeWeightedRep`; the general invertible-sector CCRA test carries only the
unbounded computability predicate, exactly as in the paper. -/
structure DecisionAlgorithms where
  minimize : WeightedRep -> WeightedRep
  invertible : WeightedRep -> Bool
  ccra : WeightedRep -> Bool
  unipotent : WeightedRep -> Bool
  unipotentCCRA : WeightedRep -> Bool
  minimize_poly : Turing.TM2ComputableInPolyTime encodeWeightedRep encodeWeightedRep minimize
  invertible_poly : Turing.TM2ComputableInPolyTime encodeWeightedRep Computability.encodeBool invertible
  ccra_computable : Turing.TM2Computable encodeWeightedRep Computability.encodeBool ccra
  unipotent_poly : Turing.TM2ComputableInPolyTime encodeWeightedRep Computability.encodeBool unipotent
  unipotentCCRA_poly : Turing.TM2ComputableInPolyTime encodeWeightedRep Computability.encodeBool unipotentCCRA

/-- Semantic correctness of all five algorithms in `DecisionAlgorithms`. -/
def DecisionAlgorithms.Correct (A : DecisionAlgorithms) : Prop :=
  (forall E : WeightedRep, WeightedRep.SameSeries E (A.minimize E) ∧
    WeightedRep.IsMinimal (A.minimize E)) ∧
  (forall E : WeightedRep, A.invertible E = true ↔ WeightedRep.IsInvertible E) ∧
  (forall E : WeightedRep, WeightedRep.IsInvertible E ->
    (A.ccra E = true ↔ C1 (WeightedRep.series E))) ∧
  (forall E : WeightedRep, A.unipotent E = true ↔ WeightedRep.IsUnipotent E) ∧
  (forall E : WeightedRep, WeightedRep.IsUnipotent E ->
    (A.unipotentCCRA E = true ↔ C1 (WeightedRep.series E)))

end Supplement
end CopylessCRA


