-- Prove2me | Definitions.Def_HypercliqueRefutation_FourClique_Supplement_OneProduct
-- name    : HypercliqueRefutation_FourClique_Supplement_OneProduct
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:25:45.655357+00:00
-- url     : https://prove2.me/theorems/332dbc4e-0de2-4969-a578-5a183b4e1099
-- title:
--   Sparse coefficients, serialized operands and one-product execution
-- statement:
--   For nonnegative integers $m,k$, define
--
--   $$
--   n_A=2^{\lfloor m/2\rfloor},\qquad n_B=\binom mk,\qquad L=n_A\sum_{i=0}^{\lfloor k/2\rfloor}\binom mi.
--   $$
--
--   Raw sparse coefficient data comprise a common natural denominator, an integer numerator for each layer, and an optional row and sign for each layer/color pair. The decoded coefficient is zero except at that optional row, where it is $+1$ or $-1$. The decoded layer weight is its numerator divided by the common denominator. The structure assumes no positivity, cancellation identity, construction time or existence theorem. A separate specification tests positivity, polynomial-in-$m$ bit lengths and the published symmetrized cancellation identity over the rationals. Zero-color data use denominator one, zero weights, and an empty coefficient table. A three-word dimension header is always emitted by the charged generator, including this case.
--
--   The operand functions are the immutable published formulas. The new definitions serialize their pair indices in row-major order, serialize the matrix families by color and row, and compute recovery from a product $P$ by
--
--   $$
--   R_D(P)=\sum_{x,y,\ell} w_\ell P[(x,\ell),y]P[(y,\ell),x].
--   $$
--
--   A one-product execution runs coefficient generation, left construction, right construction, one ordinary scalar multiplication program and recovery, with each stage charged from execution. The left constructor receives sizes, generated coefficient records and $A$ only. The right receives sizes and $B$ only. Recovery receives sizes, generated coefficient records and the product only. Total time is the sum of the five charged stage budgets and 16 fixed driver units; dimensions come from the generated header. No multiplication algorithm is assumed by these definitions.
--
--   Soft bounds use the explicit parameter $S=2+n+m+k+n_A+n_B+L$ and the form $C(1+v)(1+\lfloor\log_2 S\rfloor)^d$. The separate volumes are $n_BL$ for coefficients, $n^2Ln_B$ and $n^2n_B$ for dense operands, and $n^2L$ for recovery. The additive one permits constant overhead on empty inputs. This preserves the paper's two resources while paying for dense operand generation in the product stage.
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, The 3-Uniform Hyperclique Hypothesis is False, STOC 2027 submission #1431 (October 2026); Problem 2.2, printed/PDF p.3; Lemma 2.4, Eq.(2) and Eq.(3), p.4; Theorem 2.6 and proof, p.5; coefficient construction pp.6–7.

import Definitions.Def_HypercliqueRefutation_FourClique_WeightedProducts
import Definitions.Def_HypercliqueRefutation_FourClique_Supplement_ScalarMachine

set_option autoImplicit false

namespace HypercliqueRefutation.FourClique.Supplement

/- Chan--Itakura--Ma--Yu, STOC 2027 submission #1431 (October 2026),
   Theorem 2.6 and its operand construction, p.5; Lemma 2.4, p.4 and pp.6--7.
   These are data, encodings and operational specifications, with no existence axiom. -/
def aSize (m : ℕ) : ℕ := 2 ^ (m / 2)
def bSize (m k : ℕ) : ℕ := Nat.choose m k
def layers (m k : ℕ) : ℕ := aSize m * ∑ i ∈ Finset.range (k / 2 + 1), Nat.choose m i

def scale (n m k : ℕ) : ℕ := 2 + n + m + k + aSize m + bSize m k + layers m k

/-- Raw sparse data: a slot has at most one row, with sign +1 (true) or -1.
    No identity, constructibility or bit bound is a structure field. -/
structure SparseData (m k : ℕ) where
  denominator : ℕ
  numerator : Fin (layers m k) → ℤ
  slot : Fin (layers m k) → Fin (bSize m k) → Option (Fin (aSize m) × Bool)

def sparseH {K : Type*} [Ring K] {m k : ℕ} (D : SparseData m k)
    (l : Fin (layers m k)) (a : Fin (aSize m)) (b : Fin (bSize m k)) : K :=
  match D.slot l b with
  | none => 0
  | some (row, pos) => if row = a then (if pos then 1 else -1) else 0

def sparseW {K : Type*} [Field K] {m k : ℕ} (D : SparseData m k)
    (l : Fin (layers m k)) : K := (D.numerator l : K) / (D.denominator : K)

def signedCode (x : ℤ) : ℕ := if 0 ≤ x then 2 * x.natAbs else 2 * x.natAbs + 1

/-- Output records, not input advice. The dimension header is itself generated.
    In the zero-color case the remaining coefficient table is empty. -/
def coefficientCells {m k : ℕ} (D : SparseData m k) : List ℕ :=
  [aSize m, bSize m k, layers m k] ++ if bSize m k = 0 then [] else
    D.denominator :: ((List.finRange (layers m k)).map (fun l => signedCode (D.numerator l)) ++
      (List.finRange (layers m k)).flatMap (fun l =>
        (List.finRange (bSize m k)).map (fun b => match D.slot l b with
          | none => 0
          | some (a, pos) => 1 + 2 * a.val + if pos then 0 else 1)))

def coefficientSpec (C d : ℕ) {m k : ℕ} (D : SparseData m k) : Prop :=
  0 < D.denominator ∧
  1 + Nat.log2 (D.denominator + 1) ≤ C * (m + 1) ^ d ∧
  (∀ l, 1 + Nat.log2 ((D.numerator l).natAbs + 1) ≤ C * (m + 1) ^ d) ∧
  (bSize m k = 0 → D.denominator = 1 ∧ ∀ l, D.numerator l = 0) ∧
  CancellationIdentity (sparseH (K := ℚ) D) (sparseW (K := ℚ) D)

abbrev Family (K : Type*) (n colors : ℕ) := Fin colors → Matrix (Fin n) (Fin n) K

def familyCells {K : Type*} {n colors : ℕ} (A : Family K n colors) : List K :=
  (List.finRange colors).flatMap fun a =>
    (List.finRange n).flatMap fun x => (List.finRange n).map fun z => A a x z

def leftCells {K : Type*} {n m k : ℕ}
    (P : Matrix (Fin n × Fin (layers m k)) (Fin n × Fin (bSize m k)) K) : List K :=
  (List.finRange n).flatMap fun x => (List.finRange (layers m k)).flatMap fun l =>
    (List.finRange n).flatMap fun z => (List.finRange (bSize m k)).map fun b => P (x,l) (z,b)

def rightCells {K : Type*} {n m k : ℕ}
    (P : Matrix (Fin n × Fin (bSize m k)) (Fin n) K) : List K :=
  (List.finRange n).flatMap fun z => (List.finRange (bSize m k)).flatMap fun b =>
    (List.finRange n).map fun y => P (z,b) y

def productCells {K : Type*} {n m k : ℕ}
    (P : Matrix (Fin n × Fin (layers m k)) (Fin n) K) : List K :=
  (List.finRange n).flatMap fun x => (List.finRange (layers m k)).flatMap fun l =>
    (List.finRange n).map fun y => P (x,l) y

def recoveryValue {K : Type*} [Field K] {n m k : ℕ} (D : SparseData m k)
    (P : Matrix (Fin n × Fin (layers m k)) (Fin n) K) : K :=
  ∑ x, ∑ y, ∑ l, sparseW D l * P (x,l) y * P (y,l) x

def reductionHeader {m k : ℕ} (n : ℕ) (D : SparseData m k) : List ℕ :=
  [n,m,k] ++ coefficientCells D

def coefficientBudget (C d m k : ℕ) : ℕ :=
  ScalarMachine.softBound C d (scale 0 m k) (bSize m k * layers m k)
def leftBudget (C d n m k : ℕ) : ℕ :=
  ScalarMachine.softBound C d (scale n m k) (n ^ 2 * layers m k * bSize m k)
def rightBudget (C d n m k : ℕ) : ℕ :=
  ScalarMachine.softBound C d (scale n m k) (n ^ 2 * bSize m k)
def recoveryBudget (C d n m k : ℕ) : ℕ :=
  ScalarMachine.softBound C d (scale n m k) (n ^ 2 * layers m k)

/-- A staged executable reduction: exactly one ordinary multiplication invocation.
    Each stage starts with zero work memory and its displayed input only. The
    multiplication is an actual scalar program, with time charged from its run.
    The surrounding finite driver passes the serialized outputs between stages.
    All materialized operand entries and all coefficient records are paid for.
    The generated natural header supplies nA,nB,L; 16 extra units cover the fixed
    driver calls and dimension multiplications, without a binomial-evaluation oracle. -/
noncomputable def OneProductExecution {K : Type} [Field K] {n m k : ℕ}
    (gen left right multiply recover : ScalarMachine.Program)
    (D : SparseData m k) (A : Family K n (aSize m)) (B : Family K n (bSize m k))
    (total : ℕ) (answer : K) : Prop :=
  ∃ cT lT rT pT qT cB lB rB pB qB,
    16 + cT + lT + rT + pT + qT ≤ total ∧
    ScalarMachine.Runs (K := ℚ) gen [m,k] [] cT cB [] (coefficientCells D) ∧
    ∃ LA RB P,
      ScalarMachine.Runs left (reductionHeader n D) (familyCells A) lT lB LA ∧
      ScalarMachine.Runs right [n,m,k] (familyCells B) rT rB RB ∧
      ScalarMachine.Runs multiply [n * layers m k, n * bSize m k, n]
        (LA ++ RB) pT pB P ∧
      ScalarMachine.Runs recover (reductionHeader n D) P qT qB [answer]

end HypercliqueRefutation.FourClique.Supplement


