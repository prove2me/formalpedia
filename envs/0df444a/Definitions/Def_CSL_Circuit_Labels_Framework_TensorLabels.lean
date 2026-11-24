-- Prove2me | Definitions.Def_CSL_Circuit_Labels_Framework_TensorLabels
-- name    : CSL_Circuit_Labels_Framework_TensorLabels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:45:57.6458+00:00
-- url     : https://prove2.me/theorems/d42aa226-3d41-4778-801a-0dbedad0fd0a
-- title:
--   Coded sorting library: Circuit / Labels / Framework / TensorLabels
-- statement:
--   Module `CodedSorting.Circuit.Labels.Framework.TensorLabels` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Explicit rational tensor matrices for the gate labels of Section 4.2.
--   All ranks below are Mathlib Matrix.rank.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Labels.Framework.TensorLabels

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Labels_Framework_RankMetric
import Definitions.Def_CSL_Circuit_Framework_Circuit
import Definitions.Def_CSL_Circuit_Framework_CircuitProgram
import Definitions.Def_CSL_Circuit_Framework_CircuitCounts
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Explicit rational tensor matrices for the gate labels of Section 4.2.
All ranks below are Mathlib Matrix.rank. -/

namespace CSL.TensorLabels

open CSL.RankMetric CSL.Circuit
open CSL.CircuitProgram
open CSL.CircuitCounts
open scoped BigOperators Matrix Kronecker

variable {d : ℕ}

noncomputable def dual (T : Triple d) : Fin d → ℚ :=
  (1 / 2 : ℚ) • ((indicator T.val) ᵥ* gramMatrix)

noncomputable def column (T : Triple d) : Matrix (Fin d) Unit ℚ :=
  fun i _ => indicator T.val i

noncomputable def row (T : Triple d) : Matrix Unit (Fin d) ℚ :=
  fun _ j => dual T j

noncomputable def line (T : Triple d) : Matrix (Fin d) (Fin d) ℚ :=
  column T * row T

theorem dual_dot (S T : Triple d) :
    dotProduct (dual S) (indicator T.val) =
      (1 / 2 : ℚ) * pairing (indicator S.val) (indicator T.val) := by
  unfold dual pairing
  rw [smul_dotProduct, ← Matrix.dotProduct_mulVec]
  rfl

theorem row_column_self (T : Triple d) : row T * column T = 1 := by
  ext i j
  cases i
  cases j
  change dotProduct (dual T) (indicator T.val) = 1
  rw [dual_dot, triple_self_pairing T.val T.property]
  norm_num

theorem row_column_orthogonal (S T : Triple d) (h : side S T) :
    row S * column T = 0 := by
  ext i j
  change dotProduct (dual S) (indicator T.val) = 0
  rw [dual_dot, intersect_one_orthogonal S.val T.val S.property T.property h]
  simp

@[simp] theorem line_idempotent (T : Triple d) : line T * line T = line T := by
  unfold line
  calc
    (column T * row T) * (column T * row T) =
        column T * (row T * column T) * row T := by simp only [Matrix.mul_assoc]
    _ = column T * row T := by rw [row_column_self, Matrix.mul_one]

theorem lines_orthogonal (S T : Triple d) (h : side S T) : line S * line T = 0 := by
  unfold line
  calc
    (column S * row S) * (column T * row T) =
        column S * (row S * column T) * row T := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [row_column_orthogonal S T h]; simp

/-- A rectangular split factorization computes actual rank exactly. -/
theorem rank_of_split {n r : Type*} [Fintype n] [Fintype r] [DecidableEq r]
    (U : Matrix n r ℚ) (V : Matrix r n ℚ) (h : V * U = 1) :
    (U * V).rank = Fintype.card r := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left U V).trans U.rank_le_card_width
  · have heq : V * ((U * V) * U) = 1 := by
      calc
        V * ((U * V) * U) = (V * U) * (V * U) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h]; simp
    calc
      Fintype.card r = (1 : Matrix r r ℚ).rank := Matrix.rank_one.symm
      _ = (V * ((U * V) * U)).rank := by rw [heq]
      _ ≤ ((U * V) * U).rank := Matrix.rank_mul_le_right _ _
      _ ≤ (U * V).rank := Matrix.rank_mul_le_left _ _

/-- Rectangular variant: distinct left and right inverses suffice; the
product itself need not be a projection. -/
theorem rank_of_split_factors {n m r : Type*}
    [Fintype n] [Fintype m] [Fintype r] [DecidableEq r]
    (U : Matrix n r ℚ) (V : Matrix r m ℚ)
    (L : Matrix r n ℚ) (R : Matrix m r ℚ)
    (hL : L * U = 1) (hR : V * R = 1) :
    (U * V).rank = Fintype.card r := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left U V).trans U.rank_le_card_width
  · have heq : L * ((U * V) * R) = 1 := by
      calc
        L * ((U * V) * R) = (L * U) * (V * R) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hL, hR]; simp
    calc
      Fintype.card r = (1 : Matrix r r ℚ).rank := Matrix.rank_one.symm
      _ = (L * ((U * V) * R)).rank := by rw [heq]
      _ ≤ ((U * V) * R).rank := Matrix.rank_mul_le_right _ _
      _ ≤ (U * V).rank := Matrix.rank_mul_le_left _ _

@[simp] theorem line_rank (T : Triple d) : (line T).rank = 1 := by
  simpa [line] using rank_of_split (column T) (row T) (row_column_self T)

def tensor3 {a b c x y z : Type*}
    (A : Matrix a x ℚ) (B : Matrix b y ℚ) (C : Matrix c z ℚ) :
    Matrix (a × (b × c)) (x × (y × z)) ℚ := A ⊗ₖ (B ⊗ₖ C)

theorem tensor3_mul
    {a b c x y z p q r : Type*} [Fintype x] [Fintype y] [Fintype z]
    (A : Matrix a x ℚ) (B : Matrix b y ℚ) (C : Matrix c z ℚ)
    (D : Matrix x p ℚ) (E : Matrix y q ℚ) (F : Matrix z r ℚ) :
    tensor3 A B C * tensor3 D E F = tensor3 (A * D) (B * E) (C * F) := by
  unfold tensor3
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

@[simp] theorem tensor3_one {a b c : Type*} [DecidableEq a] [DecidableEq b]
    [DecidableEq c] :
    tensor3 (1 : Matrix a a ℚ) (1 : Matrix b b ℚ) (1 : Matrix c c ℚ) = 1 := by
  simp [tensor3, Matrix.one_kronecker_one]

theorem tensor3_rank_of_split
    {a b c x y z : Type*} [Fintype a] [Fintype b] [Fintype c]
    [Fintype x] [Fintype y] [Fintype z]
    [DecidableEq x] [DecidableEq y] [DecidableEq z]
    (U : Matrix a x ℚ) (V : Matrix x a ℚ)
    (U' : Matrix b y ℚ) (V' : Matrix y b ℚ)
    (U'' : Matrix c z ℚ) (V'' : Matrix z c ℚ)
    (h : V * U = 1) (h' : V' * U' = 1) (h'' : V'' * U'' = 1) :
    (tensor3 (U * V) (U' * V') (U'' * V'')).rank =
      Fintype.card x * (Fintype.card y * Fintype.card z) := by
  rw [← tensor3_mul]
  have hs : tensor3 V V' V'' * tensor3 U U' U'' = 1 := by
    rw [tensor3_mul, h, h', h'', tensor3_one]
  simpa using rank_of_split (tensor3 U U' U'') (tensor3 V V' V'') hs

abbrev H (d : ℕ) := Fin d × (Fin d × Fin d)
abbrev Label (d : ℕ) := Matrix (H d) (H d) ℚ

noncomputable def dataLine (a b c : Triple d) : Label d :=
  tensor3 (line a) (line b) (line c)

@[simp] theorem dataLine_idempotent (a b c : Triple d) :
    dataLine a b c * dataLine a b c = dataLine a b c := by
  simp [dataLine, tensor3_mul]

@[simp] theorem dataLine_rank (a b c : Triple d) : (dataLine a b c).rank = 1 := by
  have h := tensor3_rank_of_split (column a) (row a) (column b) (row b)
    (column c) (row c) (row_column_self a) (row_column_self b) (row_column_self c)
  simpa [dataLine, line] using h

inductive Round where
  | first | second | third
  deriving DecidableEq

/-- The two parameters are the fixed coordinates of the round's group. -/
noncomputable def unitLine (r : Round) (a b T : Triple d) : Label d :=
  match r with
  | .first => dataLine T a b
  | .second => dataLine a T b
  | .third => dataLine a b T

/-- The X subspace at the beginning of a round. -/
noncomputable def before (r : Round) (a b T : Triple d) : Label d :=
  match r with
  | .first => tensor3 (line T) (line a) (line b)
  | .second => tensor3 1 (line T) (line b)
  | .third => tensor3 1 1 (line T)

/-- The X subspace at the end of a round. -/
noncomputable def ambient (r : Round) (a b : Triple d) : Label d :=
  match r with
  | .first => tensor3 1 (line a) (line b)
  | .second => tensor3 1 1 (line b)
  | .third => tensor3 1 1 1

/-- The d-dimensional summand lost at the central 3→4 edge. -/
noncomputable def drop (r : Round) (a b : Triple d) : Label d :=
  match r with
  | .first => tensor3 1 (line a) (line b)
  | .second => tensor3 (line a) 1 (line b)
  | .third => tensor3 (line a) (line b) 1

noncomputable def base (r : Round) (a b : Triple d) : Label d :=
  ambient r a b - drop r a b

/-- This uses exactly the LocalGate nodes and port graph of CircuitProgram. -/
noncomputable def gateLabel (r : Round) (a b : Triple d) : LocalGate d → Label d
  | .g0 S => before r a b S - unitLine r a b S
  | .g1 => base r a b
  | .g2 T => base r a b + unitLine r a b T
  | .g3 => ambient r a b
  | .g4 => base r a b
  | .g5 S => ambient r a b - unitLine r a b S
  | .g6 => ambient r a b
  | .g7 _ => ambient r a b

@[simp] theorem unitLine_idempotent (r : Round) (a b T : Triple d) :
    unitLine r a b T * unitLine r a b T = unitLine r a b T := by
  cases r <;> simp [unitLine]

@[simp] theorem unitLine_rank (r : Round) (a b T : Triple d) :
    (unitLine r a b T).rank = 1 := by cases r <;> simp [unitLine]

@[simp] theorem before_idempotent (r : Round) (a b T : Triple d) :
    before r a b T * before r a b T = before r a b T := by
  cases r <;> simp [before, tensor3_mul]

@[simp] theorem ambient_idempotent (r : Round) (a b : Triple d) :
    ambient r a b * ambient r a b = ambient r a b := by
  cases r <;> simp [ambient, tensor3_mul]

@[simp] theorem drop_idempotent (r : Round) (a b : Triple d) :
    drop r a b * drop r a b = drop r a b := by
  cases r <;> simp [drop, tensor3_mul]

@[simp] theorem ambient_drop (r : Round) (a b : Triple d) :
    ambient r a b * drop r a b = drop r a b := by
  cases r <;> simp [ambient, drop, tensor3_mul]

@[simp] theorem drop_ambient (r : Round) (a b : Triple d) :
    drop r a b * ambient r a b = drop r a b := by
  cases r <;> simp [ambient, drop, tensor3_mul]

@[simp] theorem ambient_unitLine (r : Round) (a b T : Triple d) :
    ambient r a b * unitLine r a b T = unitLine r a b T := by
  cases r <;> simp [ambient, unitLine, dataLine, tensor3_mul]

@[simp] theorem unitLine_ambient (r : Round) (a b T : Triple d) :
    unitLine r a b T * ambient r a b = unitLine r a b T := by
  cases r <;> simp [ambient, unitLine, dataLine, tensor3_mul]

@[simp] theorem drop_unitLine (r : Round) (a b T : Triple d) :
    drop r a b * unitLine r a b T = unitLine r a b T := by
  cases r <;> simp [drop, unitLine, dataLine, tensor3_mul]

@[simp] theorem unitLine_drop (r : Round) (a b T : Triple d) :
    unitLine r a b T * drop r a b = unitLine r a b T := by
  cases r <;> simp [drop, unitLine, dataLine, tensor3_mul]

@[simp] theorem ambient_before (r : Round) (a b T : Triple d) :
    ambient r a b * before r a b T = before r a b T := by
  cases r <;> simp [ambient, before, tensor3_mul]

@[simp] theorem before_ambient (r : Round) (a b T : Triple d) :
    before r a b T * ambient r a b = before r a b T := by
  cases r <;> simp [ambient, before, tensor3_mul]

@[simp] theorem drop_before (r : Round) (a b T : Triple d) :
    drop r a b * before r a b T = unitLine r a b T := by
  cases r <;> simp [drop, before, unitLine, dataLine, tensor3_mul]

@[simp] theorem before_drop (r : Round) (a b T : Triple d) :
    before r a b T * drop r a b = unitLine r a b T := by
  cases r <;> simp [drop, before, unitLine, dataLine, tensor3_mul]

@[simp] theorem before_unitLine (r : Round) (a b T : Triple d) :
    before r a b T * unitLine r a b T = unitLine r a b T := by
  cases r <;> simp [before, unitLine, dataLine, tensor3_mul]

@[simp] theorem unitLine_before (r : Round) (a b T : Triple d) :
    unitLine r a b T * before r a b T = unitLine r a b T := by
  cases r <;> simp [before, unitLine, dataLine, tensor3_mul]

theorem unitLines_orthogonal (r : Round) (a b S T : Triple d) (h : side S T) :
    unitLine r a b S * unitLine r a b T = 0 := by
  cases r <;>
    simp only [unitLine, dataLine, tensor3_mul, line_idempotent, lines_orthogonal S T h]
  all_goals simp [tensor3, Matrix.zero_kronecker, Matrix.kronecker_zero]

@[simp] theorem base_idempotent (r : Round) (a b : Triple d) :
    base r a b * base r a b = base r a b := by
  simp [base, sub_mul, mul_sub]

@[simp] theorem base_ambient (r : Round) (a b : Triple d) :
    base r a b * ambient r a b = base r a b := by simp [base, sub_mul]

@[simp] theorem ambient_base (r : Round) (a b : Triple d) :
    ambient r a b * base r a b = base r a b := by simp [base, mul_sub]

@[simp] theorem base_unitLine (r : Round) (a b T : Triple d) :
    base r a b * unitLine r a b T = 0 := by simp [base, sub_mul]

@[simp] theorem unitLine_base (r : Round) (a b T : Triple d) :
    unitLine r a b T * base r a b = 0 := by simp [base, mul_sub]

/-- Every actual gate label is an idempotent rational projection matrix. -/
theorem gateLabel_idempotent (r : Round) (a b : Triple d) (g : LocalGate d) :
    gateLabel r a b g * gateLabel r a b g = gateLabel r a b g := by
  cases g <;> simp [gateLabel, sub_mul, mul_sub, add_mul, mul_add]

@[simp] theorem drop_rank (r : Round) (a b : Triple d) : (drop r a b).rank = d := by
  cases r with
  | first =>
    have h := tensor3_rank_of_split (1 : Matrix (Fin d) (Fin d) ℚ) 1
      (column a) (row a) (column b) (row b) (by simp) (row_column_self a) (row_column_self b)
    simpa [drop, line] using h
  | second =>
    have h := tensor3_rank_of_split (column a) (row a)
      (1 : Matrix (Fin d) (Fin d) ℚ) 1 (column b) (row b)
      (row_column_self a) (by simp) (row_column_self b)
    simpa [drop, line] using h
  | third =>
    have h := tensor3_rank_of_split (column a) (row a) (column b) (row b)
      (1 : Matrix (Fin d) (Fin d) ℚ) 1 (row_column_self a) (row_column_self b) (by simp)
    simpa [drop, line] using h

/-- The actual central descending edge has rank exactly d in every round. -/
theorem centre_descent_rank (r : Round) (a b : Triple d) :
    (gateLabel r a b .g3 - gateLabel r a b .g4).rank = d := by
  have h : gateLabel r a b .g3 - gateLabel r a b .g4 = drop r a b := by
    simp [gateLabel, base]
  rw [h, drop_rank]

def Nested (P Q : Label d) : Prop := P * Q = P ∧ Q * P = P

theorem nested_refl (P : Label d) (hP : P * P = P) : Nested P P := ⟨hP, hP⟩

theorem nested_trans {P Q R : Label d} (hPQ : Nested P Q) (hQR : Nested Q R) :
    Nested P R := by
  constructor
  · calc
      P * R = (P * Q) * R := by rw [hPQ.1]
      _ = P * (Q * R) := mul_assoc _ _ _
      _ = P := by rw [hQR.1, hPQ.1]
  · calc
      R * P = R * (Q * P) := by rw [hPQ.2]
      _ = (R * Q) * P := (mul_assoc _ _ _).symm
      _ = P := by rw [hQR.2, hPQ.2]

theorem nested_rank_le {P Q : Label d} (h : Nested P Q) : P.rank ≤ Q.rank := by
  have hr := Matrix.rank_mul_le_right P Q
  rwa [h.1] at hr

theorem nested_rank_difference {P Q : Label d}
    (hP : P * P = P) (hQ : Q * Q = Q) (h : Nested P Q) :
    (Q - P).rank = Q.rank - P.rank :=
  matrix_compatible_projection_rank_difference P Q hP hQ h.1 h.2

theorem nested_zero (P : Label d) : Nested 0 P := by simp [Nested]
theorem nested_one (P : Label d) : Nested P 1 := by simp [Nested]

theorem g0_g1_nested (r : Round) (a b S : Triple d) :
    Nested (gateLabel r a b (.g0 S)) (gateLabel r a b .g1) := by
  simp [Nested, gateLabel, base, sub_mul, mul_sub]

theorem g1_g2_nested (r : Round) (a b T : Triple d) :
    Nested (gateLabel r a b .g1) (gateLabel r a b (.g2 T)) := by
  simp [Nested, gateLabel, add_mul, mul_add]

theorem g2_g3_nested (r : Round) (a b T : Triple d) :
    Nested (gateLabel r a b (.g2 T)) (gateLabel r a b .g3) := by
  simp [Nested, gateLabel, add_mul, mul_add]

theorem g4_g5_nested (r : Round) (a b S : Triple d) :
    Nested (gateLabel r a b .g4) (gateLabel r a b (.g5 S)) := by
  simp [Nested, gateLabel, sub_mul, mul_sub]

theorem g5_g7_nested (r : Round) (a b S T : Triple d) :
    Nested (gateLabel r a b (.g5 S)) (gateLabel r a b (.g7 T)) := by
  simp [Nested, gateLabel, sub_mul, mul_sub]

theorem before_g2_nested (r : Round) (a b T : Triple d) :
    Nested (before r a b T) (gateLabel r a b (.g2 T)) := by
  simp [Nested, gateLabel, base, add_mul, mul_add, sub_mul, mul_sub]

theorem g2_g5_nested (r : Round) (a b S T : Triple d) (h : side S T) :
    Nested (gateLabel r a b (.g2 T)) (gateLabel r a b (.g5 S)) := by
  have hST := unitLines_orthogonal r a b S T h
  have hTS := unitLines_orthogonal r a b T S ((side_symmetric T S).mpr h)
  simp [Nested, gateLabel, add_mul, mul_add, sub_mul, mul_sub, hST, hTS]

/-- All three nontrivial inclusions along a real side register. -/
theorem side_wire_nested (r : Round) (a b : Triple d) (e : SideIndex d) :
    Nested (gateLabel r a b (.g0 e.val.1)) (gateLabel r a b (.g2 e.val.2)) ∧
    Nested (gateLabel r a b (.g2 e.val.2)) (gateLabel r a b (.g5 e.val.1)) ∧
    Nested (gateLabel r a b (.g5 e.val.1)) (gateLabel r a b (.g7 e.val.2)) := by
  exact ⟨nested_trans (g0_g1_nested r a b e.val.1) (g1_g2_nested r a b e.val.2),
    g2_g5_nested r a b e.val.1 e.val.2 e.property,
    g5_g7_nested r a b e.val.1 e.val.2⟩

def roundExponent : Round → ℕ | .first => 1 | .second => 2 | .third => 3

theorem ambient_rank (r : Round) (a b : Triple d) :
    (ambient r a b).rank = d ^ roundExponent r := by
  cases r with
  | first => simpa [ambient, drop, roundExponent] using drop_rank Round.first a b
  | second =>
    have h := tensor3_rank_of_split (1 : Matrix (Fin d) (Fin d) ℚ) 1
      (1 : Matrix (Fin d) (Fin d) ℚ) 1 (column b) (row b)
      (by simp) (by simp) (row_column_self b)
    simpa [ambient, line, roundExponent, pow_two] using h
  | third =>
    simp [ambient, roundExponent, Matrix.rank_one, H, Fintype.card_prod, pow_succ, Nat.mul_assoc]

theorem before_rank (r : Round) (a b T : Triple d) :
    (before r a b T).rank = d ^ (roundExponent r - 1) := by
  cases r with
  | first => simpa [before, dataLine, roundExponent] using dataLine_rank T a b
  | second => simpa [before, ambient, roundExponent] using ambient_rank Round.first T b
  | third => simpa [before, ambient, roundExponent] using ambient_rank Round.second a T

theorem base_rank (r : Round) (a b : Triple d) :
    (base r a b).rank = (ambient r a b).rank - d := by
  have h := nested_rank_difference (drop_idempotent r a b) (ambient_idempotent r a b)
    (show Nested (drop r a b) (ambient r a b) from ⟨drop_ambient r a b, ambient_drop r a b⟩)
  simpa [base] using h

theorem ambient_le_full_rank (r : Round) (a b : Triple d) :
    (ambient r a b).rank ≤ d ^ 3 := by
  have h := (ambient r a b).rank_le_card_width
  simpa [H, pow_succ, Nat.mul_assoc] using h

theorem rank_identity : (1 : Label d).rank = d ^ 3 := by
  simp [Matrix.rank_one, H, pow_succ, Nat.mul_assoc]

/-- The last round reaches the full identity matrix. -/
theorem last_ambient (a b : Triple d) : ambient Round.third a b = 1 := by
  simp [ambient]

/-- The first X gate is precisely the one-dimensional data projection. -/
theorem first_x_gate (a b T : Triple d) :
    gateLabel Round.first a b (.g2 T) = dataLine T a b := by
  simp [gateLabel, base, ambient, drop, unitLine]

theorem first_y_gate (a b T : Triple d) :
    gateLabel Round.first a b (.g0 T) = 0 := by
  simp [gateLabel, before, unitLine, dataLine]

theorem first_second_boundary (a b c : Triple d) :
    ambient Round.first b c = before Round.second a c b := rfl

theorem second_third_boundary (a b c : Triple d) :
    ambient Round.second a c = before Round.third a b c := rfl

theorem data_line_consistent (a b c : Triple d) :
    unitLine Round.first b c a = unitLine Round.second a c b ∧
    unitLine Round.second a c b = unitLine Round.third a b c := ⟨rfl, rfl⟩

noncomputable def chainCost (P : Label d) : List (Label d) → ℕ
  | [] => 0
  | Q :: qs => (Q - P).rank + chainCost Q qs

def chainLast (P : Label d) : List (Label d) → Label d
  | [] => P
  | Q :: qs => chainLast Q qs

def IsNestedChain (P : Label d) : List (Label d) → Prop
  | [] => P * P = P
  | Q :: qs => P * P = P ∧ Nested P Q ∧ IsNestedChain Q qs

theorem nested_chain_start {P : Label d} {qs : List (Label d)}
    (h : IsNestedChain P qs) : P * P = P := by
  cases qs with
  | nil => exact h
  | cons Q qs => exact h.1

theorem nested_chain_end {P : Label d} {qs : List (Label d)}
    (h : IsNestedChain P qs) : Nested P (chainLast P qs) := by
  induction qs generalizing P with
  | nil => exact nested_refl P h
  | cons Q qs ih => exact nested_trans h.2.1 (ih h.2.2)

theorem chainCost_telescope {P : Label d} {qs : List (Label d)}
    (h : IsNestedChain P qs) :
    chainCost P qs = (chainLast P qs).rank - P.rank := by
  induction qs generalizing P with
  | nil => simp [chainCost, chainLast]
  | cons Q qs ih =>
      have hPQ := nested_rank_le h.2.1
      have hQend := nested_rank_le (nested_chain_end h.2.2)
      have hdiff := nested_rank_difference h.1 (nested_chain_start h.2.2) h.2.1
      simp only [chainCost, chainLast, hdiff, ih h.2.2]
      omega

theorem chainCost_append (P : Label d) (xs ys : List (Label d)) :
    chainCost P (xs ++ ys) = chainCost P xs + chainCost (chainLast P xs) ys := by
  induction xs generalizing P with
  | nil => simp [chainCost, chainLast]
  | cons Q qs ih => simp [chainCost, chainLast, ih, Nat.add_assoc]

theorem chainLast_append (P : Label d) (xs ys : List (Label d)) :
    chainLast P (xs ++ ys) = chainLast (chainLast P xs) ys := by
  induction xs generalizing P with
  | nil => rfl
  | cons Q qs ih => exact ih Q

theorem nested_chain_append {P : Label d} {xs ys : List (Label d)}
    (hx : IsNestedChain P xs) (hy : IsNestedChain (chainLast P xs) ys) :
    IsNestedChain P (xs ++ ys) := by
  induction xs generalizing P with
  | nil => exact hy
  | cons Q qs ih => exact ⟨hx.1, hx.2.1, ih hx.2.2 hy⟩

noncomputable def auxiliaryCost (r : Round) (a b : Triple d) (R : LocalReg d) : ℕ :=
  chainCost 0 ((localWireVisits R).map (gateLabel r a b) ++ [1])

/-- Every actual side wire, INCLUDING its source and sink edges, costs d³. -/
theorem side_wire_total_rank (r : Round) (a b : Triple d) (e : SideIndex d) :
    auxiliaryCost r a b (.a e) = d ^ 3 := by
  obtain ⟨h02, h25, h57⟩ := side_wire_nested r a b e
  have hchain : IsNestedChain 0
      [gateLabel r a b (.g0 e.val.1), gateLabel r a b (.g2 e.val.2),
       gateLabel r a b (.g5 e.val.1), gateLabel r a b (.g7 e.val.2), 1] :=
    ⟨by simp, nested_zero _, gateLabel_idempotent _ _ _ _, h02,
      gateLabel_idempotent _ _ _ _, h25, gateLabel_idempotent _ _ _ _, h57,
      gateLabel_idempotent _ _ _ _, nested_one _, by simp [IsNestedChain]⟩
  have hcost := chainCost_telescope hchain
  simpa [auxiliaryCost, localWireVisits, chainLast, rank_identity, pow_succ, Nat.mul_assoc] using hcost

/-- Every actual centre wire costs d³ + 2d, including both terminal edges. -/
theorem centre_wire_total_rank (r : Round) (a b : Triple d) (i : Fin d) :
    auxiliaryCost r a b (.c i) = d ^ 3 + 2 * d := by
  have hBR : Nested (base r a b) (ambient r a b) :=
    ⟨base_ambient r a b, ambient_base r a b⟩
  have hRB : (ambient r a b - base r a b).rank = d := by
    simpa [gateLabel] using centre_descent_rank r a b
  have hback : (base r a b - ambient r a b).rank = d := by
    rw [matrix_rank_sub_symm, hRB]
  have hfull := nested_rank_difference (ambient_idempotent r a b)
    (show (1 : Label d) * 1 = 1 by simp) (nested_one (ambient r a b))
  have hDR : d ≤ (ambient r a b).rank := by
    have h := nested_rank_le
      (show Nested (drop r a b) (ambient r a b) from ⟨drop_ambient r a b, ambient_drop r a b⟩)
    simpa using h
  have hRm := ambient_le_full_rank r a b
  simp only [auxiliaryCost, localWireVisits, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, chainCost, gateLabel, sub_zero, add_zero]
  rw [hRB, hback, hfull, rank_identity, base_rank]
  omega

noncomputable def xRoundCost (r : Round) (a b T : Triple d) : ℕ :=
  chainCost (before r a b T) ((localWireVisits (.x T)).map (gateLabel r a b))

theorem x_round_nested (r : Round) (a b T : Triple d) :
    IsNestedChain (before r a b T)
      ((localWireVisits (.x T)).map (gateLabel r a b)) :=
    ⟨before_idempotent r a b T, before_g2_nested r a b T,
      gateLabel_idempotent _ _ _ _, g2_g3_nested r a b T,
      ambient_idempotent r a b, nested_refl _ (ambient_idempotent r a b),
      ambient_idempotent r a b, nested_refl _ (ambient_idempotent r a b),
      ambient_idempotent r a b⟩

theorem x_round_total_rank (r : Round) (a b T : Triple d) :
    xRoundCost r a b T = (ambient r a b).rank - (before r a b T).rank := by
  have hchain : IsNestedChain (before r a b T)
      [gateLabel r a b (.g2 T), gateLabel r a b .g3,
       gateLabel r a b .g6, gateLabel r a b (.g7 T)] :=
    ⟨before_idempotent r a b T, before_g2_nested r a b T,
      gateLabel_idempotent _ _ _ _, g2_g3_nested r a b T,
      ambient_idempotent r a b, nested_refl _ (ambient_idempotent r a b),
      ambient_idempotent r a b, nested_refl _ (ambient_idempotent r a b),
      ambient_idempotent r a b⟩
  simpa [xRoundCost, localWireVisits, chainLast, gateLabel] using chainCost_telescope hchain

noncomputable def yRoundCost (r : Round) (a b T : Triple d) : ℕ :=
  chainCost (before r a b T - unitLine r a b T)
    ((localWireVisits (.y T)).map (gateLabel r a b))

theorem y_round_nested (r : Round) (a b T : Triple d) :
    IsNestedChain (gateLabel r a b (.g0 T))
      ((localWireVisits (.y T)).map (gateLabel r a b)) :=
    ⟨gateLabel_idempotent _ _ _ _, nested_refl _ (gateLabel_idempotent _ _ _ _),
      gateLabel_idempotent _ _ _ _, g0_g1_nested r a b T,
      base_idempotent r a b, nested_refl _ (base_idempotent r a b),
      base_idempotent r a b, g4_g5_nested r a b T, gateLabel_idempotent _ _ _ _⟩

theorem y_round_total_rank (r : Round) (a b T : Triple d) :
    yRoundCost r a b T = (ambient r a b).rank - (before r a b T).rank := by
  have hchain : IsNestedChain (gateLabel r a b (.g0 T))
      [gateLabel r a b (.g0 T), gateLabel r a b .g1,
       gateLabel r a b .g4, gateLabel r a b (.g5 T)] :=
    ⟨gateLabel_idempotent _ _ _ _, nested_refl _ (gateLabel_idempotent _ _ _ _),
      gateLabel_idempotent _ _ _ _, g0_g1_nested r a b T,
      base_idempotent r a b, nested_refl _ (base_idempotent r a b),
      base_idempotent r a b, g4_g5_nested r a b T, gateLabel_idempotent _ _ _ _⟩
  have hcost := chainCost_telescope hchain
  have hs := nested_rank_difference (unitLine_idempotent r a b T)
    (before_idempotent r a b T) (show Nested (unitLine r a b T) (before r a b T) from
      ⟨unitLine_before r a b T, before_unitLine r a b T⟩)
  have ht := nested_rank_difference (unitLine_idempotent r a b T)
    (ambient_idempotent r a b) (show Nested (unitLine r a b T) (ambient r a b) from
      ⟨unitLine_ambient r a b T, ambient_unitLine r a b T⟩)
  have h1 : 1 ≤ (before r a b T).rank := by
    have h := nested_rank_le (show Nested (unitLine r a b T) (before r a b T) from
      ⟨unitLine_before r a b T, before_unitLine r a b T⟩)
    simpa using h
  have h2 : (before r a b T).rank ≤ (ambient r a b).rank :=
    nested_rank_le (nested_trans (before_g2_nested r a b T) (g2_g3_nested r a b T))
  simp only [unitLine_rank] at hs ht
  change yRoundCost r a b T = _
  have heq : yRoundCost r a b T =
      (ambient r a b - unitLine r a b T).rank -
        (before r a b T - unitLine r a b T).rank := by
    simpa [yRoundCost, localWireVisits, chainLast, gateLabel] using hcost
  rw [heq, hs, ht]
  omega

noncomputable def dataXPath (a b c : Triple d) : List (Label d) :=
  (localWireVisits (.x a)).map (gateLabel .first b c) ++
  (localWireVisits (.x b)).map (gateLabel .second a c) ++
  (localWireVisits (.x c)).map (gateLabel .third a b) ++ [1]

noncomputable def dataYPath (a b c : Triple d) : List (Label d) :=
  (localWireVisits (.y a)).map (gateLabel .first b c) ++
  (localWireVisits (.y b)).map (gateLabel .second a c) ++
  (localWireVisits (.y c)).map (gateLabel .third a b) ++ [1 - dataLine a b c]

theorem data_x_positive_chain (a b c : Triple d) :
    IsNestedChain (dataLine a b c) (dataXPath a b c) := by
  unfold dataXPath
  simp only [List.append_assoc]
  apply nested_chain_append (xs := (localWireVisits (.x a)).map (gateLabel .first b c))
    (x_round_nested .first b c a)
  apply nested_chain_append (xs := (localWireVisits (.x b)).map (gateLabel .second a c))
  · simpa [localWireVisits, chainLast, gateLabel, ambient, before] using x_round_nested .second a c b
  apply nested_chain_append (xs := (localWireVisits (.x c)).map (gateLabel .third a b))
  · simpa [localWireVisits, chainLast, gateLabel, ambient, before] using x_round_nested .third a b c
  simp [localWireVisits, chainLast, gateLabel, ambient, IsNestedChain, Nested]

theorem data_y_chain (a b c : Triple d) : IsNestedChain 0 (dataYPath a b c) := by
  unfold dataYPath
  simp only [List.append_assoc]
  apply nested_chain_append (xs := (localWireVisits (.y a)).map (gateLabel .first b c))
  · simpa [first_y_gate] using y_round_nested .first b c a
  apply nested_chain_append (xs := (localWireVisits (.y b)).map (gateLabel .second a c))
  · simpa [localWireVisits, chainLast, gateLabel, ambient, before, unitLine] using
      y_round_nested .second a c b
  apply nested_chain_append (xs := (localWireVisits (.y c)).map (gateLabel .third a b))
  · simpa [localWireVisits, chainLast, gateLabel, ambient, before, unitLine] using
      y_round_nested .third a b c
  have hp : (1 - dataLine a b c) * (1 - dataLine a b c) = 1 - dataLine a b c := by
    simp [sub_mul, mul_sub]
  simpa [localWireVisits, chainLast, gateLabel, ambient, unitLine] using
    (show IsNestedChain (1 - dataLine a b c) [1 - dataLine a b c] from
      ⟨hp, nested_refl _ hp, hp⟩)

/-- The entire actual X wire costs m, including the negative source edge. -/
theorem data_x_wire_total_rank (a b c : Triple d) :
    chainCost (-dataLine a b c) (dataXPath a b c) = d ^ 3 := by
  have hclean := chainCost_telescope (data_x_positive_chain a b c)
  have hlast : chainLast (dataLine a b c) (dataXPath a b c) = 1 := by
    simp [dataXPath, localWireVisits, chainLast]
  rw [hlast, rank_identity, dataLine_rank] at hclean
  have hstart : chainCost (-dataLine a b c) (dataXPath a b c) =
      1 + chainCost (dataLine a b c) (dataXPath a b c) := by
    simp only [dataXPath, localWireVisits, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, first_x_gate]
    simp only [chainCost, sub_self, Matrix.rank_zero, zero_add,
      negative_source_edge_rank, dataLine_rank]
  have hdim : 1 ≤ d ^ 3 := by
    have h := (dataLine a b c).rank_le_card_width
    simpa [H, dataLine_rank, pow_succ, Nat.mul_assoc] using h
  rw [hstart, hclean]
  omega

/-- The entire actual Y wire costs m−1, including both terminal edges. -/
theorem data_y_wire_total_rank (a b c : Triple d) :
    chainCost 0 (dataYPath a b c) = d ^ 3 - 1 := by
  have h := chainCost_telescope (data_y_chain a b c)
  have hlast : chainLast 0 (dataYPath a b c) = 1 - dataLine a b c := by
    simp [dataYPath, localWireVisits, chainLast]
  rw [hlast, Matrix.rank_zero, Nat.sub_zero] at h
  have hr := nested_rank_difference (dataLine_idempotent a b c)
    (show (1 : Label d) * 1 = 1 by simp) (nested_one (dataLine a b c))
  rw [rank_identity, dataLine_rank] at hr
  exact h.trans hr

def roundOfFin (j : Fin 3) : Round :=
  if j.val = 0 then .first else if j.val = 1 then .second else .third

noncomputable def globalSource : GlobalReg d → Label d
  | .inl (.inl a) => -dataLine a.1 a.2.1 a.2.2
  | _ => 0

noncomputable def globalSink : GlobalReg d → Label d
  | .inl (.inr a) => 1 - dataLine a.1 a.2.1 a.2.2
  | _ => 1

/-- The full matrix sequence on each real register, including its sink label. -/
noncomputable def globalWirePath : GlobalReg d → List (Label d)
  | .inl (.inl a) => dataXPath a.1 a.2.1 a.2.2
  | .inl (.inr a) => dataYPath a.1 a.2.1 a.2.2
  | .inr (j,k,.inl e) =>
      (localWireVisits (.a e)).map (gateLabel (roundOfFin j) k.1 k.2) ++ [1]
  | .inr (j,k,.inr i) =>
      (localWireVisits (.c i)).map (gateLabel (roundOfFin j) k.1 k.2) ++ [1]

noncomputable def globalNodeLabel (u : GlobalGate d) : Label d :=
  gateLabel (roundOfFin u.1) u.2.1.1 u.2.1.2 u.2.2

/-- The explicit rank-accounting paths are the labels of the chronological
register visits, with the actual sink attached. -/
theorem globalWirePath_eq_visits (r : GlobalReg d) :
    globalWirePath r = (globalWireVisits r).map globalNodeLabel ++ [globalSink r] := by
  rcases r with (a | a) | ⟨j,k,(e | i)⟩ <;>
    simp [globalWirePath, globalWireVisits, dataGateVisits, globalNodeLabel,
      globalSink, dataXPath, dataYPath, groupingAt, grouping1, grouping2, grouping3,
      slice1, slice2, slice3, roundOfFin, List.map_append, List.map_map,
      Function.comp_def]

def partner : GlobalReg d → GlobalReg d
  | .inl (.inl a) => .inl (.inr a)
  | .inl (.inr a) => .inl (.inl a)
  | .inr a => .inr a

theorem partner_involutive : Function.Involutive (partner (d := d)) := by
  intro r
  rcases r with (a | a) | a <;> rfl

/-- Every actual crossed source/sink session has identity difference. -/
theorem global_endpoint_identity (r : GlobalReg d) :
    globalSink (partner r) - globalSource r = 1 := by
  rcases r with (a | a) | a <;> simp [partner, globalSource, globalSink]

noncomputable def globalWireCost (r : GlobalReg d) : ℕ :=
  chainCost (globalSource r) (globalWirePath r)

@[simp] theorem globalWireCost_x (a : DataIndex d) :
    globalWireCost (.inl (.inl a)) = d ^ 3 := data_x_wire_total_rank _ _ _

@[simp] theorem globalWireCost_y (a : DataIndex d) :
    globalWireCost (.inl (.inr a)) = d ^ 3 - 1 := data_y_wire_total_rank _ _ _

@[simp] theorem globalWireCost_side (j : Fin 3) (k : GroupIndex d) (e : SideIndex d) :
    globalWireCost (.inr (j,k,.inl e)) = d ^ 3 :=
  side_wire_total_rank (roundOfFin j) k.1 k.2 e

@[simp] theorem globalWireCost_centre (j : Fin 3) (k : GroupIndex d) (i : Fin d) :
    globalWireCost (.inr (j,k,.inr i)) = d ^ 3 + 2 * d :=
  centre_wire_total_rank (roundOfFin j) k.1 k.2 i

noncomputable def totalRank (d : ℕ) : ℕ := ∑ r : GlobalReg d, globalWireCost r

/-- This sums ranks of all actual wire edges, not assigned per-wire budgets. -/
theorem totalRank_formula :
    totalRank d = (d.choose 3)^3 * d^3 + (d.choose 3)^3 * (d^3 - 1) +
      3 * (d.choose 3)^2 *
        ((d.choose 3) * (3 * (d-3).choose 2) * d^3 + d * (d^3 + 2*d)) := by
  unfold totalRank
  simp only [GlobalReg, Fintype.sum_sum_type, Fintype.sum_prod_type,
    globalWireCost_x, globalWireCost_y, globalWireCost_side, globalWireCost_centre,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin,
    data_registers_card, groups_card, side_registers_card]
  ring

/-- Exact rank accounting with the cardinality of the actual register type W. -/
theorem totalRank_budget_add (hd : 0 < d) :
    totalRank d + (d.choose 3)^3 =
      Fintype.card (GlobalReg d) * d^3 + 6 * (d.choose 3)^2 * d^2 := by
  have hm : 0 < d^3 := pow_pos hd _
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [totalRank_formula, all_registers_card]
  simp only [hk, Nat.succ_sub_one, Nat.succ_eq_add_one]
  ring

/-- The paper's total-rank formula, now for the concrete tensor labels and wires. -/
theorem totalRank_budget (hd : 0 < d) :
    totalRank d = Fintype.card (GlobalReg d) * d^3 - (d.choose 3)^3 +
      6 * (d.choose 3)^2 * d^2 := by
  have hm : 1 ≤ d^3 := pow_pos hd _
  have hW : (d.choose 3)^3 ≤ Fintype.card (GlobalReg d) := by
    rw [all_registers_card]
    omega
  have hmul := Nat.mul_le_mul_left (Fintype.card (GlobalReg d)) hm
  simp only [Nat.mul_one] at hmul
  have hsub := Nat.sub_add_cancel (hW.trans hmul)
  have heq := totalRank_budget_add hd
  omega

theorem concrete_strict_saving :
    totalRank 46 < Fintype.card (GlobalReg 46) * 46^3 := by
  rw [totalRank_budget (by norm_num), all_registers_card]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

/-- Labels after every program stage, including private pass vertices.
An inactive gate leaves this register's label unchanged. -/
noncomputable def stageLabels {G : Type*} (active : G → Bool) (label : G → Label d)
    (P : Label d) : List G → List (Label d)
  | [] => []
  | g :: gs =>
    let Q := if active g then label g else P
    Q :: stageLabels active label Q gs

/-- Subdividing a wire by pass vertices adds only zero-rank edges. -/
theorem stageLabels_cost {G : Type*} (active : G → Bool) (label : G → Label d)
    (gs : List G) (P T : Label d) :
    chainCost P (stageLabels active label P gs ++ [T]) =
      chainCost P ((gs.filter active).map label ++ [T]) := by
  induction gs generalizing P with
  | nil => rfl
  | cons g gs ih =>
    by_cases hg : active g = true
    · simp [stageLabels, hg, chainCost, ih]
    · have hfalse : active g = false := Bool.eq_false_iff.mpr hg
      simp [stageLabels, hfalse, chainCost, ih]

/-- Cost on every literal gate stage, with private pass vertices retained. -/
noncomputable def programStageWireCost (r : GlobalReg d) : ℕ :=
  chainCost (globalSource r)
    (stageLabels (fun u => decide (r ∈ (globalNodeGate u).ports)) globalNodeLabel
      (globalSource r) (globalGateOrder d) ++ [globalSink r])

/-- This is the bridge to the real program: visits are obtained by filtering
the actual ports in its full chronological node order. -/
theorem programStageWireCost_eq (r : GlobalReg d) :
    programStageWireCost r = globalWireCost r := by
  unfold programStageWireCost globalWireCost
  rw [stageLabels_cost, ← globalWireVisits_eq_filter, ← globalWirePath_eq_visits]

theorem programStage_totalRank :
    (∑ r : GlobalReg d, programStageWireCost r) = totalRank d := by
  simp [programStageWireCost_eq, totalRank]

end CSL.TensorLabels


