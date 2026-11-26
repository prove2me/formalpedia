-- Prove2me | Definitions.Def_GRH_DyadicCharacterGrid
-- name    : GRH_DyadicCharacterGrid
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T18:45:15.270685+00:00
-- url     : https://prove2.me/theorems/c08cc8ee-cb98-5ab0-a343-313b84528955
-- title:
--   Symmetry-reduced finite Dirichlet grids and dyadic heights
-- statement:
--   A character is selected by the sign of its first nonreal residue. The reduced grid tests one column when its horizontal extent is zero and the upper rows for a self-conjugate character. Heights are indexed by powers of two.
-- source:
--   Derived for the centered Möbius theorem in the Masullo mission. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_GRH_DirichletGrid

namespace GRH.DyadicCharacterGrid
open DirichletGrid

/-- Real characters and the member of each nonreal conjugate pair whose first
nonreal residue has positive imaginary part. -/
def Oriented {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  (∀ n : ℕ, n<q → (χ (n:ZMod q)).im=0) ∨ ∃ n<q, 0<(χ (n:ZMod q)).im ∧
    ∀ j<n, (χ (j:ZMod q)).im=0

/-- The original finite test at one sample point. -/
def Cell {q : ℕ} (χ : DirichletCharacter ℂ q) (a b H : ℝ) (m i j : ℕ) : Prop :=
  ((q=3 ∨ q=4) ∧ |(point a b H m i j).im|+(1+2*H)/m ≤ 1/(256*(q:ℝ))) ∨
    budget q H/m < ‖sample χ m (point a b H m i j)‖

/-- On a vertical line only one column is needed. A self-conjugate character
needs only the rows at or above the horizontal midpoint. -/
def Checks {q : ℕ} (χ : DirichletCharacter ℂ q) (a b H : ℝ) (m : ℕ) : Prop :=
  0<m ∧ ∀ i≤m, ∀ j≤m, (a≠b ∨ i=0) → (χ≠χ⁻¹ ∨ m≤2*j) → Cell χ a b H m i j

def index (k : ℕ) : ℕ := 2^k-1

noncomputable def left (b : ℝ) (h : ℕ) : ℝ := 1/2+(b-1/2)/((h:ℝ)+1)

end GRH.DyadicCharacterGrid


