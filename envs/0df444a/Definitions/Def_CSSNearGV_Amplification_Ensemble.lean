-- Prove2me | Definitions.Def_CSSNearGV_Amplification_Ensemble
-- name    : CSSNearGV_Amplification_Ensemble
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T21:16:22.15382+00:00
-- url     : https://prove2.me/theorems/22a703d8-3099-44a2-80b6-bb50292cd307
-- title:
--   Binary parity ensemble and derived CSS spaces
-- statement:
--   Work over $\mathbb F_2$ with $n=sb$ consecutively ordered coordinates. The block repetition space consists of vectors constant on each block, and its binary orthogonal complement is the block parity space. Let $A$ be noncyclic prefix summation and $D$ its noncyclic inverse derivative. Independent uniform coordinate permutations are sampled from the finite product of $2m$ permutation groups.
--
--   The AD order applies $A$ before $D$ in each round. The DA order applies $D$ before $A$. The classical code is the image of the parity space. From the same AD matrix $L$ define
--   $$S_X=L\widetilde R_s,\qquad S_Z=L^{-\mathsf T}\widetilde R_s.$$
--
--   The quantum subspace uses the published CSS span definition with inputs $S_Z^\perp$ and $S_X^\perp$. Logical lower bounds quantify over the corresponding orthogonal complements minus the stabilizer spaces. The finite weight enumerators and transition probabilities count actual words under the uniform permutation law. Orthogonality, ranks, code dimension and distances are properties to prove, not fields in a supplied code.
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Section 2 and Section 3.1, printed pp.4–9 / PDF 6–11

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification
attribute [local instance] Classical.propDecidable

abbrev Bit := ZMod 2
abbrev Word (n : ℕ) := Fin n → Bit
abbrev BinCode (n : ℕ) := Submodule Bit (Word n)
abbrev Perms (n m : ℕ) := Fin (2 * m) → Equiv.Perm (Fin n)

def weight {n : ℕ} (x : Word n) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0).card

/-- Block constant words, with consecutively ordered blocks of length s. -/
def repetition (s b : ℕ) : BinCode (s * b) :=
  Submodule.span Bit {x | ∃ y : Fin b → Bit, ∀ i, x i = y ⟨i.val / s, by
    have hi := i.isLt
    exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hi)⟩}

/-- Orthogonality to each block indicator is exactly even parity in each block. -/
def parity (s b : ℕ) : BinCode (s * b) := QAlgorithms.binDual (repetition s b)

def accumulationMatrix (n : ℕ) : Matrix (Fin n) (Fin n) Bit :=
  fun i j => if j ≤ i then 1 else 0

def derivativeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) Bit :=
  fun i j => if j = i ∨ j.val + 1 = i.val then 1 else 0

def permMatrix {n : ℕ} (p : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) Bit :=
  fun i j => if i = p j then 1 else 0

/-- `true` is the paper's AD order: A first, D second. -/
def roundMatrix {n : ℕ} (ad : Bool) (p q : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) Bit :=
  if ad then derivativeMatrix n * permMatrix q * accumulationMatrix n * permMatrix p
  else accumulationMatrix n * permMatrix q * derivativeMatrix n * permMatrix p

def amplifier {n m : ℕ} (ad : Bool) (π : Perms n m) : Matrix (Fin n) (Fin n) Bit :=
  ((List.finRange m).map fun i => roundMatrix ad
    (π ⟨2 * i.val, by omega⟩) (π ⟨2 * i.val + 1, by omega⟩)).foldl (fun M T => T * M) 1

def imageCode {n : ℕ} (M : Matrix (Fin n) (Fin n) Bit) (C : BinCode n) : BinCode n :=
  C.map M.mulVecLin

def classicalCode (s b m : ℕ) (ad : Bool) (π : Perms (s * b) m) : BinCode (s * b) :=
  imageCode (amplifier ad π) (parity s b)

def sx (s b m : ℕ) (π : Perms (s * b) m) : BinCode (s * b) :=
  imageCode (amplifier true π) (repetition s b)

def sz (s b m : ℕ) (π : Perms (s * b) m) : BinCode (s * b) :=
  imageCode (amplifier true π)⁻¹.transpose (repetition s b)

/-- Same convention as the published CSS definition: C1=Sz perpendicular, C2=Sx perpendicular. -/
def quantumCode (s b m : ℕ) (π : Perms (s * b) m) :=
  QAlgorithms.cssCode (QAlgorithms.binDual (sz s b m π)) (QAlgorithms.binDual (sx s b m π))

def logicalBounds (s b m : ℕ) (π : Perms (s * b) m) (d : ℝ) : Prop :=
  (∀ x ∈ QAlgorithms.binDual (sz s b m π), x ∉ sx s b m π → d ≤ (weight x : ℝ)) ∧
  (∀ z ∈ QAlgorithms.binDual (sx s b m π), z ∉ sz s b m π → d ≤ (weight z : ℝ))

def cssParameters (s b m : ℕ) (π : Perms (s * b) m) : Prop :=
  sx s b m π ≤ QAlgorithms.binDual (sz s b m π) ∧
  Module.finrank Bit (sx s b m π) = b ∧ Module.finrank Bit (sz s b m π) = b ∧
  Module.finrank ℂ (quantumCode s b m π) = 2 ^ ((s - 2) * b)

/-- Exact independent uniform sampling, a finite product of permutation sets. -/
def average {n m : ℕ} (f : Perms n m → ℝ) : ℝ :=
  (∑ π, f π) / Fintype.card (Perms n m)

def probability {n m : ℕ} (E : Perms n m → Prop) : ℝ :=
  average fun π => if E π then 1 else 0

def phiFinite (s b a : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Word (s * b) => x ∈ parity s b ∧ weight x = a).card

def enumerator (s b m : ℕ) (ad : Bool) (c : ℕ) : ℝ :=
  average fun π : Perms (s * b) m =>
    ((Finset.univ.filter fun x : Word (s * b) => x ∈ classicalCode s b m ad π ∧ weight x = c).card : ℝ)

/-- Uniform transition from a fixed canonical word of weight a; a≤n is the domain. -/
def transition (n : ℕ) (acc : Bool) (a c : ℕ) : ℝ :=
  (∑ p : Equiv.Perm (Fin n), if weight
    (((if acc then accumulationMatrix n else derivativeMatrix n) * permMatrix p).mulVec
      (fun i => if i.val < a then 1 else 0)) = c then (1 : ℝ) else 0) /
    Fintype.card (Equiv.Perm (Fin n))

def distanceAtLeast {n : ℕ} (C : BinCode n) (d : ℝ) : Prop :=
  ∀ x ∈ C, x ≠ 0 → d ≤ (weight x : ℝ)

def distanceGreater {n : ℕ} (C : BinCode n) (d : ℝ) : Prop :=
  ∀ x ∈ C, x ≠ 0 → d < (weight x : ℝ)

end CSSNearGV.Amplification


