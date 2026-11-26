-- Prove2me | Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
-- name    : CSeparatedNPComplete_PolynomialCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:47:43.654801+00:00
-- url     : https://prove2.me/theorems/10d0e758-d912-445c-ba1a-cbdd744455bf
-- title:
--   Polynomial Certificate
-- statement:
--   Definitions and structural lemmas for Polynomial Certificate, from Tomislav Prusina (tomo61098/c-separated-np-complete-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Fixed-threshold Gaussian c-separation gadget equivalence and square-partition reduction development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CSeparatedNPComplete.PolynomialCertificate
def binaryCost (x y : ℕ) : ℕ := 8 * (Nat.size x + Nat.size y + 1)
structure Totals where
  leftCount : ℕ
  rightCount : ℕ
  leftSum : ℕ
  rightSum : ℕ
  work : ℕ
  deriving DecidableEq, Repr
def run : List (ℕ × Bool) → Totals
  | [] => ⟨0, 0, 0, 0, 0⟩
  | (w, b) :: xs =>
    let r := run xs
    if b then
      ⟨r.leftCount + 1, r.rightCount, r.leftSum + w, r.rightSum,
        r.work + binaryCost r.leftCount 1 + binaryCost r.leftSum w + 1⟩
    else
      ⟨r.leftCount, r.rightCount + 1, r.leftSum, r.rightSum + w,
        r.work + binaryCost r.rightCount 1 + binaryCost r.rightSum w + 1⟩
def bitMass (r : Totals) : ℕ :=
  Nat.size r.leftCount + Nat.size r.rightCount + Nat.size r.leftSum + Nat.size r.rightSum
def budget (xs : List (ℕ × Bool)) : ℕ :=
  (xs.map fun p => Nat.size p.1 + 3).sum
def leftCount (xs : List (ℕ × Bool)) : ℕ := (xs.map fun p => if p.2 then 1 else 0).sum
def rightCount (xs : List (ℕ × Bool)) : ℕ := (xs.map fun p => if p.2 then 0 else 1).sum
def leftSum (xs : List (ℕ × Bool)) : ℕ := (xs.map fun p => if p.2 then p.1 else 0).sum
def rightSum (xs : List (ℕ × Bool)) : ℕ := (xs.map fun p => if p.2 then 0 else p.1).sum
def tagged {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) : List (ℕ × Bool) :=
  List.ofFn fun i => (s i, b i)
def encodeWeight (w : ℕ) : List Bool :=
  (w.bits.flatMap fun b => [false, b]) ++ [true, true]
def encodeInput {n : ℕ} (s : Fin n → ℕ) : List Bool :=
  (List.ofFn s).flatMap encodeWeight
def inputBits {n : ℕ} (s : Fin n → ℕ) : ℕ := 2 * ∑ i, (Nat.size (s i) + 1)
def certificate {n : ℕ} (b : Fin n → Bool) : List Bool := List.ofFn b
def verify {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) : Bool :=
  let r := run (tagged s b)
  (r.leftCount == r.rightCount) && (r.leftSum == r.rightSum)
def verificationWork {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) : ℕ :=
  let r := run (tagged s b)
  inputBits s + n + r.work + binaryCost r.leftCount r.rightCount + binaryCost r.leftSum r.rightSum + 1
def selector {n : ℕ} (b : Fin n → Bool) : Vec n := fun i => if b i then 1 else 0
end CSeparatedNPComplete.PolynomialCertificate


