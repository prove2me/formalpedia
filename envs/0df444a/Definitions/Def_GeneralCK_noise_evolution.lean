-- Prove2me | Definitions.Def_GeneralCK_noise_evolution
-- name    : GeneralCK_noise_evolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T21:51:09.427173+00:00
-- url     : https://prove2.me/theorems/bd9a22a6-e66f-4915-86bb-86b6122a08e6
-- title:
--   Continuous-time Boolean noise and coordinate flips
-- statement:
--   For time $t\in\mathbb R$, the crossover parameter is $p(t)=(1-e^{-2t})/2$. For a real-valued function $v$ on the finite Boolean cube, the noise operator is $T_pv(y)=\sum_xK_p(x,y)v(x)$, where $K_p$ is the independent-coordinate noise kernel. The bundle defines a single-coordinate flip, its inverse equivalence, and the one-coordinate kernel factor. The embedded flip involution proof establishes the inverse law used by the equivalence.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/NoiseEvolution.lean#L7-L151

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
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
namespace GeneralCK.Noise
open scoped BigOperators

noncomputable def crossover (t : ℝ) : ℝ := (1 - Real.exp (-2 * t)) / 2

noncomputable def applyNoise {n : ℕ} (p : ℝ) (v : Cube n → ℝ) (y : Cube n) : ℝ :=
  ∑ x, noiseKernel p x y * v x

def flip {n : ℕ} (y : Cube n) (i : Fin n) : Cube n := Function.update y i (!(y i))



noncomputable def factor (p : ℝ) (a b : Bool) : ℝ := if a = b then 1 - p else p































@[simp] theorem flip_flip {n : ℕ} (y : Cube n) (i : Fin n) :
    flip (flip y i) i = y := by
  funext j
  by_cases h : j = i
  · subst j; simp [flip]
  · simp [flip, h]

def flipEquiv {n : ℕ} (i : Fin n) : Cube n ≃ Cube n where
  toFun y := flip y i
  invFun y := flip y i
  left_inv y := flip_flip y i
  right_inv y := flip_flip y i



end GeneralCK.Noise


