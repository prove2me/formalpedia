-- Prove2me | Definitions.Def_GeneralCK_cube_analysis
-- name    : GeneralCK_cube_analysis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T21:51:15.022398+00:00
-- url     : https://prove2.me/theorems/1113864c-6ef7-4dbd-933a-5e7e6408dae1
-- title:
--   Uniform cube averages and recursive Bellman energy
-- statement:
--   For a function $v:\{0,1\}^n\to\mathbb R$, its uniform mean is $2^{-n}\sum_xv(x)$. The two slices fix the first coordinate, and consEquiv identifies the $(n+1)$-cube with the product of a Boolean coordinate and the $n$-cube. The recursive energy averages the two slice energies and adds the mean interior edge cost between corresponding slice values. These exact definitions support the induction from the finite Bellman inequality to a bound on every finite cube.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CubeAnalysis.lean#L7-L58

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
namespace GeneralCK.CubeAnalysis
open scoped BigOperators

noncomputable def mean {n : ℕ} (v : Cube n → ℝ) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) * ∑ x, v x

def slice {n : ℕ} (v : Cube (n+1) → ℝ) (b : Bool) : Cube n → ℝ :=
  fun x => v (Fin.cons b x)

def consEquiv (n : ℕ) : Bool × Cube n ≃ Cube (n+1) where
  toFun x := Fin.cons x.1 x.2
  invFun x := (x 0, Fin.tail x)
  left_inv x := by cases x; simp
  right_inv x := by simp















/-- Recursive edge energy, with the same normalization as manuscript Lemma 1.3. -/
noncomputable def energy : (n : ℕ) → (Cube n → ℝ) → ℝ
  | 0, _ => 0
  | n+1, v => (energy n (slice v false) + energy n (slice v true)) / 2 +
      mean (fun x => interiorCost (slice v false x) (slice v true x))







end GeneralCK.CubeAnalysis


