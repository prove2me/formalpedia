-- Prove2me | Definitions.Def_ExactFourier
-- name    : ExactFourier
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:10.840418+00:00
-- url     : https://prove2.me/theorems/50e1c9b5-2603-4210-a42e-937fc76c6f84
-- statement:
--   For each nonnegative integer n, a scalar circuit starts with n complex inputs and an additional zero value. Each charged gate adds or subtracts two available values, or multiplies an available value by a predetermined complex coefficient. A program is a finite, topologically ordered sequence of such gates; every gate appends its result while retaining all earlier values. A circuit specifies a program and n outputs selected from the available values, allowing output permutations, repeated outputs, and arbitrary reuse without additional charge. Its size is its number of gates, with no restrictions on coefficient magnitudes, storage, or conditioning. The Fourier matrix has entries Fₙ(j,k)=ζₙ^(jk) for 0≤j,k<n, where ζₙ=exp(2πi/n); this is the unnormalized transform with positive exponential sign. A circuit computes a matrix A when its output equals Ax for every complex input vector x. MainStatement is the defined proposition that, for every real c>0 and every integer N₀≥2, there exist an integer n≥N₀ and a circuit computing Fₙ exactly whose size is strictly less than c n log₂(n). Thus the proposition asks for arbitrarily small normalized circuit size along arbitrarily large dimensions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ExactFourier.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ExactFourier.lean; bytes 16..1927
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
Scalar circuits for exact discrete Fourier transforms.
No bounds on predetermined complex coefficients, reuse, storage, or conditioning.
-/

namespace ExactFourier

/-- One charged scalar gate, referencing only available values. -/
inductive Gate (w : ℕ) where
  | add (i j : Fin w)
  | sub (i j : Fin w)
  | scale (c : ℂ) (i : Fin w)

def Gate.eval {w : ℕ} (v : Fin w → ℂ) : Gate w → ℂ
  | .add i j => v i + v j
  | .sub i j => v i - v j
  | .scale c i => c * v i

/-- A topologically ordered scalar DAG; available values are never consumed. -/
inductive Program (n : ℕ) : ℕ → Type where
  | nil : Program n 0
  | step {k : ℕ} (p : Program n k) (g : Gate (n + 1 + k)) : Program n (k + 1)

def Program.eval {n : ℕ} : {k : ℕ} → Program n k → (Fin n → ℂ) →
    (Fin (n + 1 + k) → ℂ)
  | 0, .nil, x => Fin.snoc x 0
  | _ + 1, .step p g, x =>
      let v := p.eval x
      Fin.snoc v (g.eval v)

/-- Outputs name available values, so permutations and arbitrary fanout are uncharged. -/
structure Circuit (n : ℕ) where
  size : ℕ
  program : Program n size
  outputs : Fin n → Fin (n + 1 + size)

def Circuit.eval {n : ℕ} (C : Circuit n) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun i => C.program.eval x (C.outputs i)

noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
noncomputable def fourierMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => zeta n ^ (j.val * k.val)

def Circuit.Computes {n : ℕ} (C : Circuit n) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x, C.eval x = A.mulVec x

/-- The precise quantified formulation of source theorem `thm:main`. -/
def MainStatement : Prop :=
  ∀ c : ℝ, 0 < c → ∀ N₀ : ℕ, 2 ≤ N₀ → ∃ n : ℕ, N₀ ≤ n ∧
    ∃ C : Circuit n, C.Computes (fourierMatrix n) ∧
      (C.size : ℝ) < c * (n : ℝ) * Real.logb 2 (n : ℝ)



end ExactFourier
end OAI


