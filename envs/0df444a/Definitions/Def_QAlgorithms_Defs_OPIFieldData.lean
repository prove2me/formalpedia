-- Prove2me | Definitions.Def_QAlgorithms_Defs_OPIFieldData
-- name    : QAlgorithms_Defs_OPIFieldData
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:21:13.268091+00:00
-- url     : https://prove2.me/theorems/2a313d49-a972-4284-9332-9a62b1378e43
-- title:
--   OPIFieldData
-- statement:
--   OPIFieldData
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\OPIFieldData.lean

import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_Defs_OPIBitPrograms
import Definitions.Def_QAlgorithms_Defs_FieldCodeGeometry
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.OPI

open Complexity

/-- Public polynomial-basis field presentation with explicit bit algorithms;
2607.14650 pp.16–17, 2607.16541 p.7, 2610.02145 pp.15–16.
Algorithms are data independent of hidden sets; their bit execution is charged.
The defining polynomial and basis are part of the public input. -/
structure publicFieldEncoding (F : Type) [Field F] [Fintype F] where
  p : ℕ
  prime : p.Prime
  e : ℕ
  e_pos : 0 < e
  characteristic : ringChar F = p
  cardinality : Fintype.card F = p^e
  modulus : Polynomial (ZMod p)
  modulus_degree : modulus.natDegree = e
  modulus_monic : modulus.Monic
  modulus_irreducible : Irreducible modulus
  coordinates : F ≃ (Fin e → ZMod p)
  generator : F
  polynomialBasis : ∀ a, a = ∑ j, ((coordinates a j).val : F)*generator^j.val
  root : ∑ j ∈ modulus.support, ((modulus.coeff j).val : F)*generator^j = 0
  arithmetic : Fin 4 → BitOracleProgram
  arithmetic_public : ∀ op, IsPublicPreprocessor (arithmetic op)

/-- Fixed-width polynomial-basis encoding, most significant bits first;
2607.14650 pp.16–17, 2607.16541 p.7. -/
def fieldBits {F : Type} [Field F] [Fintype F] (E : publicFieldEncoding F) (a : F) : Str :=
  (List.ofFn fun j => List.ofFn (natToBits (Nat.clog 2 E.p) (E.coordinates a j).val)).flatten

/-- Arithmetic execution and cost contract for the explicitly stored programs;
2607.14650 pp.16–17. Correctness is required of an effective presentation,
not silently granted to an arbitrary enumeration. Operations are add/sub/mul/inverse. -/
def EffectiveFieldEncoding {F : Type} [Field F] [Fintype F] (E : publicFieldEncoding F) : Prop :=
  ∃ bound : Polynomial ℕ, ∀ op a b,
    ∃ fuel, fuel ≤ bound.eval (E.e*Nat.clog 2 E.p+1) ∧
      let result := bitProgramExecution (E.arithmetic op)
        (fieldBits E a ++ fieldBits E b) (fun _ => false) (fun _ => false) fuel
      result.status = some true ∧
        result.output = fieldBits E
          (if op = 0 then a+b else if op = 1 then a-b else if op = 2 then a*b else a⁻¹) ∧
        result.time ≤ bound.eval (E.e*Nat.clog 2 E.p+1) ∧
        result.visited.card ≤ bound.eval (E.e*Nat.clog 2 E.p+1)

/-- Total coefficient decoding in the public polynomial basis; 2607.16541 p.7,
2610.02145 pp.14,16,20. Consecutive fixed-width coefficient coordinates use the
same basis as fieldBits. Invalid digits are reduced modulo p, and missing bits
are zero. This is output interpretation, not an uncharged field-operation gate. -/
def coefficientOutput {F : Type} [Field F] [Fintype F]
    (E : publicFieldEncoding F) (k : ℕ) (bits : Str) : Fin k → F :=
  fun i => E.coordinates.symm fun j =>
    (bitsToNat (fun a : Fin (Nat.clog 2 E.p) =>
      bits.getD ((i.val*E.e+j.val)*Nat.clog 2 E.p+a.val) false) : ZMod E.p)

/-- Public OPI binary input; no hidden set table is encoded;
2607.14650 pp.3,16–19, 2607.16541 p.7. Target is an integer accepted-coordinate count. -/
def publicInputEncoding {F : Type} [Field F] [Fintype F]
    (E : publicFieldEncoding F) (m k target : ℕ) (alpha : Fin m → F) : Str :=
  LocalHamiltonian.encBin E.p ++ LocalHamiltonian.encBin E.e ++
    (List.ofFn fun j : Fin (E.e+1) => LocalHamiltonian.encBin (E.modulus.coeff j.val).val).flatten ++
    LocalHamiltonian.encBin m ++ LocalHamiltonian.encBin k ++ LocalHamiltonian.encBin target ++
      (List.ofFn fun i => fieldBits E (alpha i)).flatten

/-- Canonical coefficient polynomial, including zero and lower degree;
2607.14650 p.19, 2610.02145 p.10 (2.9). -/
def coefficientPolynomial {F : Type*} [Field F] {k : ℕ} (x : Fin k → F) : Polynomial F :=
  ∑ j, Polynomial.monomial j.val (x j)

/-- Constructed Vandermonde encoder; 2607.16541 p.6 (6), 2610.02145 pp.10–11. -/
def vandermondeEncoder {F : Type*} [Field F] {m : ℕ} (alpha : Fin m → F) (k : ℕ) :
    Matrix (Fin m) (Fin k) F :=
  Matrix.of fun i j => alpha i^j.val

/-- Accepted scalar-coordinate fraction on positive length;
2607.16541 p.7 (7), 2607.14650 p.19. -/
def score {F : Type*} [Field F] {m k : ℕ} (_hm : 0 < m)
    (alpha : Fin m → F) (S : Fin m → Finset F) (x : Fin k → F) : ℝ :=
  ((Finset.univ.filter fun i => (coefficientPolynomial x).eval (alpha i) ∈ S i).card : ℝ)/m

/-- OPI solution relation on the actual polynomial;
2607.14650 p.3, Problem 1. Strict degree bound includes the zero polynomial. -/
def IsSolution {F : Type*} [Field F] {m : ℕ} (k target : ℕ)
    (alpha : Fin m → F) (S : Fin m → Finset F) (P : Polynomial F) : Prop :=
  P.degree < (k : WithBot ℕ) ∧ target ≤
    (Finset.univ.filter fun i => P.eval (alpha i) ∈ S i).card

/-- Prime-field public data with a known common nontrivial cardinality;
2607.16541 pp.6–7. Hidden sets are kept outside this object. -/
structure PrimePublicData where
  p : ℕ
  prime : p.Prime
  m : ℕ
  n : ℕ
  n_pos : 0 < n
  n_lt : n < m
  m_le : m ≤ p
  alpha : Fin m → ZMod p
  distinct : Function.Injective alpha
  c : ℕ
  c_pos : 0 < c
  c_lt : c < p

example {F : Type} [Field F] [Fintype F] (E : publicFieldEncoding F) :
    coefficientOutput E 0 [] = (0 : Fin 0 → F) := by
  funext i
  exact Fin.elim0 i

example {F : Type*} [Field F] (x : Fin 0 → F) : coefficientPolynomial x = 0 := by
  simp [coefficientPolynomial]

example {F : Type*} [Field F] {m : ℕ} (alpha : Fin m → F) (i : Fin m) :
    vandermondeEncoder alpha 1 i 0 = 1 := by simp [vandermondeEncoder]

end QAlgorithms.OPI


