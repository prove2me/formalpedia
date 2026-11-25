-- Prove2me | Definitions.Def_PandoraKnapsack_NormalizedPacking
-- name    : PandoraKnapsack_NormalizedPacking
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-25T17:24:24.802701+00:00
-- url     : https://prove2.me/theorems/9c99f8cd-271c-4b69-bca9-9208d51644cb
-- title:
--   Bounded projected-row algorithm for normalized fractional packing
-- statement:
--   For bounded packing rows and profits in $[0,1]$, test the guesses $k/8$ up to the number of columns. At each violated row take a projected separating step of size $1/(8(d+1))$ in the $d$-dimensional cube. Keep the best successful approximate candidate after rescaling by $8/9$. The explicit fuel is $64(d+1)^2+1$ per guess.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#A2.SS1, Appendix B.1 and Theorem 5.1: original constructive approximate packing subroutine for the formalized arithmetic-cost model. Projected subgradient principle as in Shor, Minimization Methods for Non-Differentiable Functions (1985), Chapter 2.

import Mathlib

/-! A bounded arithmetic algorithm for fractional packing with normalized rows and profits.
Each iteration scans the rows and projects onto the unit cube, using only
arithmetic and comparisons. -/
namespace PandoraPacking
noncomputable section

abbrev Vec (d : ℕ) := Fin d → ℝ

def dot {d : ℕ} (a x : Vec d) : ℝ := ∑ j, a j * x j

def Cube {d : ℕ} (x : Vec d) : Prop := ∀ j, 0 ≤ x j ∧ x j ≤ 1

def clip (v : ℝ) : ℝ := max 0 (min 1 v)

def rate (d : ℕ) : ℝ := 1 / (8 * (d+1 : ℕ))

def update {d : ℕ} (a x : Vec d) : Vec d := fun j => clip (x j - rate d * a j)

def energy {d : ℕ} (x y : Vec d) : ℝ := ∑ j, (x j - y j)^2

def potential {d : ℕ} (x y : Vec d) : ℝ := 64 * (d+1 : ℕ) * energy x y

structure Row (d : ℕ) where
  coeff : Vec d
  bound : ℝ

def badRow {d : ℕ} (rows : List (Row d)) (x : Vec d) : Option (Row d) :=
  rows.find? (fun q => decide (q.bound + 1/8 < dot q.coeff x))

def iterate {d : ℕ} (rows : List (Row d)) : ℕ → Vec d → Option (Vec d)
  | 0, _ => none
  | fuel+1, x =>
    match badRow rows x with
    | none => some x
    | some q => iterate rows fuel (update q.coeff x)

abbrev Matrix (r d : ℕ) := Fin r → Vec d

def Feasible {r d : ℕ} (A : Matrix r d) (x : Vec d) : Prop :=
  Cube x ∧ ∀ i, dot (A i) x ≤ 1

def rowsFor {r d : ℕ} (A : Matrix r d) (c : Vec d) (g : ℝ) : List (Row d) :=
  ⟨fun j => -(c j), -g⟩ :: (List.finRange r).map (fun i => ⟨A i,1⟩)

def fuelBound (d : ℕ) := 64*(d+1)^2+1

def scale {d : ℕ} (x : Vec d) : Vec d := fun j => (8/9) * x j

def trial {r d : ℕ} (A : Matrix r d) (c : Vec d) (k : ℕ) : Vec d :=
  match iterate (rowsFor A c ((k:ℝ)/8)) (fuelBound d) 0 with
  | none => 0
  | some x => scale x

def better {d : ℕ} (c x y : Vec d) : Vec d := if dot c x < dot c y then y else x

/-- Compare each guess exactly once, starting with the zero plan. -/
def search {r d : ℕ} (A : Matrix r d) (c : Vec d) : ℕ → Vec d
  | 0 => 0
  | k+1 => better c (search A c k) (trial A c k)

def solve {r d : ℕ} (A : Matrix r d) (c : Vec d) : Vec d := search A c (8*d+1)

end
end PandoraPacking


