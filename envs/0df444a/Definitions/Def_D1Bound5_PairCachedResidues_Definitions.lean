-- Prove2me | Definitions.Def_D1Bound5_PairCachedResidues_Definitions
-- name    : D1Bound5_PairCachedResidues_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:54:07.657287+00:00
-- url     : https://prove2.me/theorems/d93b0db5-1d2f-483c-a897-19f816121c4f
-- title:
--   Pair Cached Residues
-- statement:
--   Canonical coordinate residues at one positive modulus. They are computed once per vertex and stored as ordinary natural numbers in a certificate. The named objects in this bundle include `pairCoordinateResidues`, `pairResidueMaskBool`, `pairCoordinateSignature`, `pairCachedCoordinateSieveBool`, `PairResidueVertex`, `PairResidueVertex.signature`, `PairResidueVertex.vertex`, `pairCachedHasSquareRoot` and 2 further declarations.
-- source:
--   D1Bound5/PairCachedResidues.lean, lines 5-8, SHA-256 8d30539028d401e948637a33f705cb33707d8ad4e1fe939eafd5ed7c690a9100; D1Bound5/PairCachedResidues.lean, lines 10-19, SHA-256 8d30539028d401e948637a33f705cb33707d8ad4e1fe939eafd5ed7c690a9100; D1Bound5/PairCachedResidues.lean, lines 33-35, SHA-256 8d30539028d401e948637a33f705cb33707d8ad4e1fe939eafd5ed7c690a9100; D1Bound5/PairCachedResidues.lean, lines 37-45, SHA-256 8d30539028d401e948637a33f705cb33707d8ad4e1fe939eafd5ed7c690a9100; D1Bound5/PairCachedResidues.lean, lines 64-67, SHA-256 8d30539028d401e948637a33f705cb33707d8ad4e1fe939eafd5ed7c690a9100; D1Bound5/PairCachedResidues.lean, lines 69-74, SHA-256 8d30539028d401e948637a33f705cb33707d8ad4e1fe939eafd5ed7c690a9100; D1Bound5/PairCachedResidues.lean, lines 85-92, SHA-256 8d30539028d401e948637a33f705cb33707d8ad4e1fe939eafd5ed7c690a9100; D1Bound5/PairCachedResidues.lean, lines 125-131, SHA-256 8d30539028d401e948637a33f705cb33707d8ad4e1fe939eafd5ed7c690a9100. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions

section
namespace D1Bound5

/-- Canonical coordinate residues at one positive modulus. They are computed
once per vertex and stored as ordinary natural numbers in a certificate. -/
def pairCoordinateResidues {tau nu : ℤ} (k : ℕ) (z : QuadInt tau nu) : ℕ × ℕ :=
  ((z.re : ZMod (k + 1)).val, (z.im : ZMod (k + 1)).val)

/-- The existing square mask applied to the product-plus-one coordinates,
computed entirely from two supplied pairs of small residues. -/
def pairResidueMaskBool (tau nu : ℤ) (k mask : ℕ) (u v : ℕ × ℕ) : Bool :=
  mask.testBit
    (((u.1 : ZMod (k + 1)) * (v.1 : ZMod (k + 1)) +
        (-(nu : ZMod (k + 1))) * (u.2 : ZMod (k + 1)) * (v.2 : ZMod (k + 1)) + 1).val *
      (k + 1) +
      ((u.1 : ZMod (k + 1)) * (v.2 : ZMod (k + 1)) +
        (u.2 : ZMod (k + 1)) * (v.1 : ZMod (k + 1)) +
        (tau : ZMod (k + 1)) * (u.2 : ZMod (k + 1)) * (v.2 : ZMod (k + 1))).val)



def pairCoordinateSignature {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (z : QuadInt tau nu) : List (ℕ × ℕ) :=
  sieve.map fun item => pairCoordinateResidues item.1 z

/-- The original ordered sieve evaluated on cached residues. Malformed or
truncated signatures are rejected, never accepted by a default lookup. -/
def pairCachedCoordinateSieveBool (tau nu : ℤ) :
    List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ) → Bool
  | [], [], [] => true
  | (k, mask) :: sieve, u :: us, v :: vs =>
      pairResidueMaskBool tau nu k mask u v &&
        pairCachedCoordinateSieveBool tau nu sieve us vs
  | _, _, _ => false



/-- A stored vertex and its untrusted modular signature. -/
structure PairResidueVertex (tau nu : ℤ) where
  vertex : QuadInt tau nu
  signature : List (ℕ × ℕ)

/-- The huge integral product and exact root test are evaluated only after
all cached modular masks accept the pair. -/
def pairCachedHasSquareRoot {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (x y : PairResidueVertex tau nu) : Bool :=
  pairCachedCoordinateSieveBool tau nu sieve x.signature y.signature &&
    QuadInt.hasSquareRoot (x.vertex * y.vertex + 1)



/-- The accepted independent-class checker with its pair test replaced by
the computationally equivalent cached test. Repetitions still cause no edge. -/
def pairCachedIndependentBool {tau nu : ℤ} (sieve : List (ℕ × ℕ)) :
    List (PairResidueVertex tau nu) → Bool
  | [] => true
  | x :: xs =>
      (xs.all fun y => if decide (x.vertex = y.vertex) then true
        else !(pairCachedHasSquareRoot sieve x y)) && pairCachedIndependentBool sieve xs



/-- The full certificate validates exact vertex-list coverage and every
signature before using the cached independent-class computation. -/
def pairCachedIndependentCertificateBool {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (vertices : List (QuadInt tau nu)) (cached : List (PairResidueVertex tau nu)) : Bool :=
  decide (cached.map PairResidueVertex.vertex = vertices) &&
    ((cached.all fun x => decide (x.signature = pairCoordinateSignature sieve x.vertex)) &&
      pairCachedIndependentBool sieve cached)



end D1Bound5
end


