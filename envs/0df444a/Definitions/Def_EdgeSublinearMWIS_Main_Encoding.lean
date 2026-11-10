-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_Encoding
-- name    : EdgeSublinearMWIS_Main_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:40:15.737291+00:00
-- url     : https://prove2.me/theorems/d0bb4e22-5314-4745-a2cf-c40c3ad79034
-- title:
--   Self-delimiting graph and signed rational encodings
-- statement:
--   Natural numbers are encoded by a unary prefix giving the length of their little-endian binary expansion, a delimiter, and those binary digits. Integers add a sign bit. A rational input supplies any signed numerator and positive denominator; reduction to lowest terms is not required. The graph encoding contains the size header and upper-triangular adjacency bits. A weighted input then contains all rational weight encodings and the accuracy encoding, in label order.
--
--   $$\ell=|\operatorname{enc}(w_0)\cdots\operatorname{enc}(w_{n-1})\operatorname{enc}(\varepsilon)|.$$
--   Output sets are full membership masks. Sparse path lists carry encoded vertex sequences and rational coefficients. The referenced finite-program model supplies actual halting executions; it contains no correctness or runtime field. All parsing, normalization and serialization must be charged by the implementation theorems.
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Theorem 2 explanatory paragraph; §5.3; §6, p.2 (PDF p.2), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Programs

namespace EdgeSublinearMWIS.Main

abbrev Program := NOFSeparation750.CodedGIP.FiniteProgram
abbrev Runs := NOFSeparation750.CodedGIP.OutputsWithin

/-- Positive denominators need not be reduced. Normalization is charged to execution. -/
structure RationalCode where
  numerator : ℤ
  denominator : ℕ
  positive : 0 < denominator

def RationalCode.value (q : RationalCode) : ℚ := q.numerator / (q.denominator : ℚ)

def natBits (n : ℕ) : List Bool := (Nat.digits 2 n).map (fun b => b == 1)

def encodeNat (n : ℕ) : List Bool :=
  List.replicate (natBits n).length true ++ [false] ++ natBits n

def encodeInt (z : ℤ) : List Bool := [decide (z < 0)] ++ encodeNat z.natAbs

def RationalCode.bits (q : RationalCode) : List Bool :=
  encodeInt q.numerator ++ encodeNat q.denominator

def encodeRat (q : ℚ) : List Bool := encodeInt q.num ++ encodeNat q.den

noncomputable def graphBits {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool := by
  classical
  exact encodeNat n ++ (List.finRange n).flatMap (fun u =>
    ((List.finRange n).filter (fun v => u < v)).map (fun v => decide (G.Adj u v)))

def mask {n : ℕ} (I : Finset (Fin n)) : List Bool :=
  List.ofFn (fun v => decide (v ∈ I))

def rationalData {n : ℕ} (w : Fin n → RationalCode) (ε : RationalCode) : List Bool :=
  ((List.ofFn (fun v => (w v).bits)).flatten) ++ ε.bits

noncomputable def weightedInput {n : ℕ} (G : SimpleGraph (Fin n))
    (w : Fin n → RationalCode) (ε : RationalCode) : List Bool :=
  graphBits G ++ rationalData w ε

def encodeSubset {n : ℕ} (I : Finset (Fin n)) : List Bool := mask I

def encodePath {n : ℕ} (p : List (Fin n)) : List Bool :=
  encodeNat p.length ++ (p.flatMap (fun v => encodeNat v.val))

def encodeSparsePaths {n : ℕ} (f : List (List (Fin n) × ℚ)) : List Bool :=
  encodeNat f.length ++ f.flatMap (fun e => encodePath e.1 ++ encodeRat e.2)

/-- Actual executions; no clock, correctness or halting field is part of Program. -/
def Evaluates (P : Program) (input output : List Bool) : Prop :=
  ∃ t : ℕ, Runs P input output t

end EdgeSublinearMWIS.Main


