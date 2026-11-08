-- Prove2me | Definitions.Def_ProperHalfspace_Cube
-- name    : ProperHalfspace_Cube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:54.551593+00:00
-- url     : https://prove2.me/theorems/ef0b7ffb-b379-40cb-aba5-5d00bae8459b
-- title:
--   The Boolean cube $\{\pm1\}^n$, its uniform expectation and probability, Boolean and bounded functions
-- statement:
--   The cube $\{\pm1\}^n$ with the uniform probability measure. For $g:\{\pm1\}^n\to\mathbb R$,
--   $$\mathbf E_x[g(x)]=2^{-n}\sum_{x\in\{\pm1\}^n}g(x),$$
--   and $\Pr_x[A(x)]$ is the expectation of the indicator of $A$. A function is Boolean if it takes values in $\{\pm1\}$, and bounded if it takes values in $[-1,1]$.
--
--   These are the objects on which every cube-level statement of the mission is written.
--
--   **Formalization Note** A point of the cube is `Fin n → ℤˣ`, with 0-based coordinates, read into $\mathbb R$ coordinatewise. Expectations are finite sums, so no integrability question arises.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), §2, pp.10–11

import Mathlib

namespace ProperHalfspace

/-!
# The Boolean cube with the uniform measure

De, Mossel, Nadimpalli, Neeman, *Efficient Proper Agnostic Learning of Halfspaces*, arXiv:2611.02344
(Nov. 1, 2026), §2, pp.10–11.

**Formalization Note.** `Cube n := Fin n → ℤˣ` is `{±1}ⁿ`, with 0-based coordinates; a point is read into `ℝ` by `coord`.
The uniform expectation and probability are finite sums, so there is no measure and no junk integral here.
-/

/-- The cube `{±1}ⁿ`. -/
abbrev Cube (n : ℕ) := Fin n → ℤˣ

/-- The `i`-th coordinate `xᵢ ∈ {±1}` of a cube point, read as a real number. -/
def coord {n : ℕ} (x : Cube n) (i : Fin n) : ℝ := ((x i : ℤ) : ℝ)

/-- The uniform expectation `E_x[g(x)] = 2⁻ⁿ Σ_x g(x)` on the cube (p.11). -/
noncomputable def cubeAvg {n : ℕ} (g : Cube n → ℝ) : ℝ := ((2 : ℝ) ^ n)⁻¹ * ∑ x : Cube n, g x

open Classical in
/-- The uniform probability `Pr_x[A(x)]` of an event on the cube. -/
noncomputable def cubeProb {n : ℕ} (A : Cube n → Prop) : ℝ := cubeAvg fun x => if A x then 1 else 0

/-- `f` is Boolean: `f : {±1}ⁿ → {±1}`, as a real-valued function. -/
def IsBoolean {n : ℕ} (f : Cube n → ℝ) : Prop := ∀ x, f x = 1 ∨ f x = -1

/-- `f` is bounded by one: `f : {±1}ⁿ → [−1, 1]`. -/
def IsBoundedOne {n : ℕ} (f : Cube n → ℝ) : Prop := ∀ x, |f x| ≤ 1

end ProperHalfspace


