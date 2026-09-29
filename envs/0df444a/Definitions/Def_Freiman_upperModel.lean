-- Prove2me | Definitions.Def_Freiman_upperModel
-- name    : Freiman_upperModel
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:37:05.895779+00:00
-- url     : https://prove2.me/theorems/eea0eecc-90f8-4d7d-96f3-ba226752c2da
-- title:
--   Freiman's upper-ray deletion trees and padded central models
-- statement:
--   Exact finite-state data for the five normal-deletion rows in Part IV; restricted continued fractions, their two hulls, the physical binary deletion tree, central words and truncations padded by the digit 3. The predicate upperModel records a finite alphabet, a prescribed central value and a strict uniform bound at every noncentral position of every padded truncation.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. Labels m2a:rule, m2a:theta, the five-row binary-deletion table, and m2a:completed-bounds.

import Definitions.Def_Freiman_prefixEval
import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Definitions.Def_Freiman_gapThreshold
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Fib.Basic

namespace Freiman

structure upperInterval where
  left : ℝ
  right : ℝ

def upperIntervalSet (I : upperInterval) : Set ℝ := Set.Icc I.left I.right
def upperLength (I : upperInterval) : ℝ := I.right - I.left

structure upperSplit where
  parent : upperInterval
  left : upperInterval
  right : upperInterval

def upperNormalSplit (I L R : upperInterval) : Prop :=
  I.left = L.left ∧ I.right = R.right ∧
  L.right < R.left ∧ 0 < upperLength L ∧ 0 < upperLength R ∧
  R.left - L.right ≤ upperLength L ∧ R.left - L.right ≤ upperLength R

def upperDerived (C D : upperInterval) : Set ℝ :=
  Set.Icc (C.left + D.left)
    (C.left + D.left + 2 * min (upperLength C) (upperLength D)) ∪
  Set.Icc (C.right + D.right - 2 * min (upperLength C) (upperLength D))
    (C.right + D.right)

def upperNormalTree (T : List Bool → upperInterval) : Prop :=
  ∀ w, upperNormalSplit (T w) (T (w ++ [false])) (T (w ++ [true]))

def upperMesh (T : List Bool → upperInterval) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ w : List Bool,
    N ≤ w.length → upperLength (T w) ≤ ε

def upperTreeSet (T : List Bool → upperInterval) : Set ℝ :=
  {x | ∀ n : ℕ, ∃ w : List Bool, w.length = n ∧ x ∈ upperIntervalSet (T w)}

def upperSumSet (K L : Set ℝ) : Set ℝ :=
  {z | ∃ x ∈ K, ∃ y ∈ L, z = x + y}

def upperPath (T S : List Bool → upperInterval)
    (u v : ℕ → List Bool) (z : ℝ) : Prop :=
  u 0 = [] ∧ v 0 = [] ∧
  (∀ n, z ∈ upperDerived (T (u n)) (S (v n))) ∧
  ∀ n,
    (upperLength (S (v n)) ≤ upperLength (T (u n)) ∧
      ∃ b, u (n + 1) = u n ++ [b] ∧ v (n + 1) = v n) ∨
    (upperLength (T (u n)) ≤ upperLength (S (v n)) ∧
      ∃ b, v (n + 1) = v n ++ [b] ∧ u (n + 1) = u n)

noncomputable def upperTheta1 : ℝ := (Real.sqrt 21 - 3) / 2
noncomputable def upperTheta2 : ℝ := (1 + Real.sqrt 21) / 10
noncomputable def upperTheta3 : ℝ := (9 - Real.sqrt 21) / 10
noncomputable def upperTheta4 : ℝ := (Real.sqrt 21 - 1) / 10
noncomputable def upperTheta5 : ℝ := (11 + Real.sqrt 21) / 50
noncomputable def upperTheta6 : ℝ := (Real.sqrt 21 - 3) / 6
noncomputable def upperTheta7 : ℝ := (13 + Real.sqrt 21) / 74
noncomputable def upperTheta8 : ℝ := (5 - Real.sqrt 21) / 2

noncomputable def upperRows (i : Fin 5) : upperSplit :=
  match i.val with
  | 0 => ⟨⟨upperTheta8, upperTheta1⟩, ⟨upperTheta8, upperTheta3⟩,
      ⟨upperTheta2, upperTheta1⟩⟩
  | 1 => ⟨⟨upperTheta8, upperTheta3⟩, ⟨upperTheta8, upperTheta5⟩,
      ⟨upperTheta4, upperTheta3⟩⟩
  | 2 => ⟨⟨upperTheta8, upperTheta5⟩, ⟨upperTheta8, upperTheta7⟩,
      ⟨upperTheta6, upperTheta5⟩⟩
  | 3 => ⟨⟨upperTheta6, upperTheta1⟩, ⟨upperTheta6, upperTheta3⟩,
      ⟨upperTheta2, upperTheta1⟩⟩
  | _ => ⟨⟨upperTheta6, upperTheta3⟩, ⟨upperTheta6, upperTheta5⟩,
      ⟨upperTheta4, upperTheta3⟩⟩

noncomputable def upperImage (w : List ℕ+) (I : upperInterval) : upperInterval :=
  ⟨min (prefixEval w I.left) (prefixEval w I.right),
   max (prefixEval w I.left) (prefixEval w I.right)⟩

noncomputable def upperImageSplit (w : List ℕ+) (D : upperSplit) : upperSplit :=
  if w.length % 2 = 0 then
    ⟨upperImage w D.parent, upperImage w D.left, upperImage w D.right⟩
  else
    ⟨upperImage w D.parent, upperImage w D.right, upperImage w D.left⟩

structure upperState where
  word : List ℕ+
  row : Fin 5

def upperNextState (s : upperState) (physicalRight : Bool) : upperState :=
  let b := if s.word.length % 2 = 0 then physicalRight else !physicalRight
  match s.row.val, b with
  | 0, false => ⟨s.word, 1⟩
  | 0, true => ⟨s.word ++ [1], 3⟩
  | 1, false => ⟨s.word, 2⟩
  | 1, true => ⟨s.word ++ [2], 3⟩
  | 2, false => ⟨s.word ++ [4], 0⟩
  | 2, true => ⟨s.word ++ [3], 0⟩
  | 3, false => ⟨s.word, 4⟩
  | 3, true => ⟨s.word ++ [1], 3⟩
  | _, false => ⟨s.word ++ [3], 0⟩
  | _, true => ⟨s.word ++ [2], 3⟩

def upperStateAt (s : upperState) (w : List Bool) : upperState :=
  w.foldl upperNextState s

noncomputable def upperTree (p : List ℕ+) (k : Fin 5) (w : List Bool) : upperInterval :=
  let s := upperStateAt ⟨p, k⟩ w
  upperImage s.word (upperRows s.row).parent

def upperAdmissible (b : ℕ → ℕ+) : Prop :=
  (∀ n, (b n : ℕ) ≤ 4) ∧
  ∀ n, (b n : ℕ) ≤ 2 → (b (n + 1) : ℕ) ≤ 3

def upperKA : Set ℝ :=
  {x | ∃ b : ℕ → ℕ+, upperAdmissible b ∧ x = cfValue b}
def upperKB : Set ℝ :=
  {x | ∃ b : ℕ → ℕ+, upperAdmissible b ∧ (b 0 : ℕ) ≤ 3 ∧ x = cfValue b}
noncomputable def upperKOne : Set ℝ := (fun x : ℝ => 1 / (1 + x)) '' upperKB

def upperOne (b : ℕ → ℕ+) : ℕ → ℕ+
  | 0 => 1
  | n + 1 => b n

def upperCentral (n : ℕ+) (l r : ℕ → ℕ+) (i : ℤ) : ℕ+ :=
  if i = 0 then n else if 0 < i then r (i.toNat - 1) else l ((-i).toNat - 1)

def upperPad (a : ℤ → ℕ+) (j : ℕ) (i : ℤ) : ℕ+ :=
  if i.natAbs ≤ j then a i else 3

noncomputable def upperInward (a : ℤ → ℕ+) (i : ℤ) : ℝ :=
  if 0 < i then cfValue (fun n => a (i - (n : ℤ) - 1))
  else cfValue (fun n => a (i + (n : ℤ) + 1))

noncomputable def upperOutward (a : ℤ → ℕ+) (i : ℤ) : ℝ :=
  if 0 < i then cfValue (fun n => a (i + (n : ℤ) + 1))
  else cfValue (fun n => a (i - (n : ℤ) - 1))

noncomputable def upperInwardFixed : ℝ := -2 + 4 * Real.sqrt 3 / 3
noncomputable def upperSmallBound : ℝ := 4 + upperTheta1 + upperInwardFixed

def upperModel (t : ℝ) : Prop :=
  ∃ a : ℤ → ℕ+, ∃ D : ℝ, ∃ N : ℕ,
    (∀ i, (a i : ℕ) ≤ N) ∧ localValue a 0 = t ∧ D < t ∧
    ∀ j i, i ≠ 0 → localValue (upperPad a j) i ≤ D

end Freiman


