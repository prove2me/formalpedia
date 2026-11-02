-- Prove2me | Definitions.Def_friedmann_simplex
-- name    : friedmann_simplex
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-02T05:10:29.896508+00:00
-- url     : https://prove2.me/theorems/be4224df-eba4-4f7f-adb8-3f30da8e34b0
-- title:
--   Rational primal simplex and cyclic entering-variable selection
-- statement:
--   Rational standard-form LPs, nonsingular feasible bases and their actual basic solutions, reduced costs, minimum-ratio pivots, boundedness, and Cunningham entering-variable order with a retained cursor.
-- source:
--   Avis and Friedmann, Mathematical Programming2017, §4.1; https://arxiv.org/abs/1305.3944

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

/-! Rational standard-form primal simplex: maximize cᵀx subject to Ax=b, x≥0.
No pivot rule or lower bound is included in the data. The inverse is Mathlib's
total matrix inverse; every permitted basis explicitly has nonzero determinant.
-/
namespace FriedmannSimplex

open scoped BigOperators
open Matrix

structure LP (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℚ
  b : Fin m → ℚ
  c : Fin n → ℚ

abbrev Basis (m n : ℕ) := Fin m → Fin n

def basisMatrix {m n : ℕ} (P : LP m n) (B : Basis m n) :
    Matrix (Fin m) (Fin m) ℚ := fun i j => P.A i (B j)

noncomputable def basicValues {m n : ℕ} (P : LP m n) (B : Basis m n) :
    Fin m → ℚ := (basisMatrix P B)⁻¹ *ᵥ P.b

noncomputable def basicPoint {m n : ℕ} (P : LP m n) (B : Basis m n) :
    Fin n → ℚ := fun j => ∑ i : Fin m, if B i = j then basicValues P B i else 0

def feasible {m n : ℕ} (P : LP m n) (x : Fin n → ℚ) : Prop :=
  P.A *ᵥ x = P.b ∧ ∀ j, 0 ≤ x j

noncomputable def basicFeasible {m n : ℕ} (P : LP m n) (B : Basis m n) : Prop :=
  Function.Injective B ∧ (basisMatrix P B).det ≠ 0 ∧ ∀ i, 0 ≤ basicValues P B i

def objective {m n : ℕ} (P : LP m n) (x : Fin n → ℚ) : ℚ :=
  ∑ j : Fin n, P.c j * x j

noncomputable def basicObjective {m n : ℕ} (P : LP m n) (B : Basis m n) : ℚ :=
  objective P (basicPoint P B)

noncomputable def direction {m n : ℕ} (P : LP m n) (B : Basis m n)
    (j : Fin n) : Fin m → ℚ :=
  (basisMatrix P B)⁻¹ *ᵥ (fun i => P.A i j)

noncomputable def reducedCost {m n : ℕ} (P : LP m n) (B : Basis m n)
    (j : Fin n) : ℚ :=
  P.c j - ∑ i : Fin m, P.c (B i) * direction P B j i

noncomputable def improving {m n : ℕ} (P : LP m n) (B : Basis m n)
    (j : Fin n) : Prop :=
  (∀ i, B i ≠ j) ∧ 0 < reducedCost P B j

noncomputable def leaving {m n : ℕ} (P : LP m n) (B : Basis m n)
    (j : Fin n) (l : Fin m) : Prop :=
  0 < direction P B j l ∧
    ∀ i, 0 < direction P B j i →
      basicValues P B l / direction P B j l ≤
        basicValues P B i / direction P B j i

noncomputable def pivot {m n : ℕ} (P : LP m n) (B : Basis m n)
    (j : Fin n) (B' : Basis m n) : Prop :=
  basicFeasible P B ∧ improving P B j ∧
    ∃ l, leaving P B j l ∧ B' = Function.update B l j ∧ basicFeasible P B'

noncomputable def optimalBasis {m n : ℕ} (P : LP m n) (B : Basis m n) : Prop :=
  basicFeasible P B ∧ ∀ j, ¬ improving P B j

noncomputable def nondegenerate {m n : ℕ} (P : LP m n) : Prop :=
  ∀ B, basicFeasible P B → ∀ i, 0 < basicValues P B i

def bounded {m n : ℕ} (P : LP m n) : Prop :=
  ∃ R : ℚ, ∀ x, feasible P x → ∀ j, |x j| ≤ R

/-- Distance from the last selected rank. A basic variable cannot enter again,
so including the last rank in the scan agrees with resuming just after it. -/
def cyclicDistance {n : ℕ} (order : Fin n ≃ Fin n) (last j : Fin n) : ℕ :=
  ((order j).val + n - last.val) % n

noncomputable def cunninghamChoice {m n : ℕ} (P : LP m n)
    (order : Fin n ≃ Fin n) (B : Basis m n) (last j : Fin n) : Prop :=
  improving P B j ∧ ∀ k, improving P B k →
    cyclicDistance order last j ≤ cyclicDistance order last k

structure State (m n : ℕ) where
  basis : Basis m n
  last : Fin n

noncomputable def cunninghamStep {m n : ℕ} (P : LP m n)
    (order : Fin n ≃ Fin n) (s s' : State m n) : Prop :=
  ∃ j, cunninghamChoice P order s.basis s.last j ∧
    pivot P s.basis j s'.basis ∧ s'.last = order j

/-- A finite complete run. The endpoint is genuinely optimal; every edge is an
actual ratio-test simplex pivot. Strictness is a conclusion of source targets. -/
noncomputable def cunninghamRun {m n : ℕ} (P : LP m n)
    (order : Fin n ≃ Fin n) (s : ℕ → State m n) (T : ℕ) : Prop :=
  basicFeasible P (s 0).basis ∧
    (∀ t, t < T → cunninghamStep P order (s t) (s (t + 1))) ∧
    optimalBasis P (s T).basis

end FriedmannSimplex


