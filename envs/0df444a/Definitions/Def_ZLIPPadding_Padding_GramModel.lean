-- Prove2me | Definitions.Def_ZLIPPadding_Padding_GramModel
-- name    : ZLIPPadding_Padding_GramModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:10.130999+00:00
-- url     : https://prove2.me/theorems/fb7b6c6a-179a-4249-9ae5-fad772050747
-- title:
--   Promised Gram inputs, lattice symmetries and exact coordinate answers
-- statement:
--   Let $n$ be positive. Integer vectors are columns and matrices act on the left. A Gram input $G$ is valid exactly when
--   $$G=M^TM\quad\text{for some }M\in\mathrm{GL}_n(\mathbb Z).$$
--   The existential factor is hidden. Unimodularity means having a two-sided integer inverse. The squared norm of coordinates $a$ is $a^TGa$; a unit answer has norm squared one, and a basis answer is a unimodular $A$ with $A^TGA=I$.
--
--   For nonzero $a$, the positive coordinate gcd determines the primitive part $a/\gcd(a)$. Screening rejects zero and accepts this primitive part exactly when its squared norm is one. The definition also introduces support sizes, full signed-permutation actions, arbitrary real orthogonal rotations, their rotated integer lattices, and the orthogonal automorphism group. These objects supply one shared coordinate model for the entire mission.
--
--   **Formalization Note** Indices are zero based. The gcd of the zero vector is defined as zero, but the screen rejects zero before dividing. Ambient geometry uses real matrix equations, without imposing the sup norm on coordinate arrays.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed pp. 6–9, 27–30 (PDF pp. 7–10, 28–31), §§2.1–2.3, (7.1)–(7.2), (7.9), (7.15)

import Mathlib

namespace ZLIPPadding.Padding
open scoped BigOperators
abbrev ZVec (n : ℕ) := Fin n → ℤ
abbrev ZMat (n : ℕ) := Matrix (Fin n) (Fin n) ℤ
abbrev RMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
/-- Integer inverse, with no bound on entries or conditioning. -/
def Unimodular {n : ℕ} (M : ZMat n) : Prop :=
  ∃ W : ZMat n, M * W = 1 ∧ W * M = 1
/-- The factor is existential, and is never supplied to an executable program. -/
def ValidGram {n : ℕ} (G : ZMat n) : Prop :=
  0 < n ∧ ∃ M : ZMat n, Unimodular M ∧ G = M.transpose * M

def qnorm {n : ℕ} (G : ZMat n) (a : ZVec n) : ℤ :=
  ∑ i, a i * (G.mulVec a) i

def UnitAnswer {n : ℕ} (G : ZMat n) (a : ZVec n) : Prop := qnorm G a = 1

def BasisAnswer {n : ℕ} (G A : ZMat n) : Prop :=
  Unimodular A ∧ A.transpose * G * A = 1

def coordGcd {n : ℕ} (a : ZVec n) : ℕ :=
  (List.ofFn fun i => (a i).natAbs).foldl Nat.gcd 0

def primitive {n : ℕ} (a : ZVec n) : ZVec n := fun i => a i / (coordGcd a : ℤ)

def screen {n : ℕ} (G : ZMat n) (a : ZVec n) : Option (ZVec n) :=
  if a = 0 then none else if qnorm G (primitive a) = 1 then some (primitive a) else none

def supportSize {n : ℕ} (a : ZVec n) : ℕ :=
  (Finset.univ.filter fun i => a i ≠ 0).card

def retainedSize {N : ℕ} (n : ℕ) (z : ZVec N) : ℕ :=
  (Finset.univ.filter fun i => i.val < n ∧ z i ≠ 0).card

def signedAction {n : ℕ} (p : Equiv.Perm (Fin n)) (s : Fin n → Bool)
    (a : ZVec n) : ZVec n := fun i => (if s i then -1 else 1) * a (p i)

def signedOrbit {n : ℕ} (a : ZVec n) : Set (ZVec n) :=
  {z | ∃ p : Equiv.Perm (Fin n), ∃ s : Fin n → Bool, z = signedAction p s a}

def Orthogonal {n : ℕ} (O : RMat n) : Prop := O.transpose * O = 1

def integerLattice {n : ℕ} (O : RMat n) : Set (Fin n → ℝ) :=
  {x | ∃ z : ZVec n, x = O.mulVec (fun i => (z i : ℝ))}

def latticeAut {n : ℕ} (O : RMat n) : Set (RMat n) :=
  {Q | Orthogonal Q ∧ Q.mulVec '' integerLattice O = integerLattice O}

/-- Every permutation and all independent signs; no rationality restriction. -/
def signedMatrices (n : ℕ) : Set (RMat n) :=
  {P | ∃ p : Equiv.Perm (Fin n), ∃ s : Fin n → Bool,
    ∀ i j, P i j = if j = p i then (if s i then -1 else 1) else 0}

end ZLIPPadding.Padding


