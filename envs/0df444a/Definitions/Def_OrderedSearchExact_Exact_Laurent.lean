-- Prove2me | Definitions.Def_OrderedSearchExact_Exact_Laurent
-- name    : OrderedSearchExact_Exact_Laurent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:25.187972+00:00
-- url     : https://prove2.me/theorems/29bc2904-8142-4a9d-8225-15972258f600
-- title:
--   Normalized symmetric Laurent coefficients, parity paths and exactification
-- statement:
--   For $n\ge1$, a real vector $a=(a_1,\ldots,a_{n-1})$ represents
--
--   $$q_a(z)=1+\sum_{j=1}^{n-1}a_j(z^j+z^{-j}),\qquad q_a(e^{i\theta})=1+2\sum_{j=1}^{n-1}a_j\cos(j\theta).$$
--
--   Reversal is $(Ja)_j=a_{n-j}$ and $P_\pm a=(a\pm Ja)/2$. Nonnegativity means nonnegativity at every real angle. A feasible prefix starts at the Fejér vector $1-j/n$, has circle integral $2\pi$ and nonnegative values at every step, and has reversal-symmetric increments on odd steps and reversal-antisymmetric increments on even steps. A feasible path also ends at the zero coefficient vector, representing the constant polynomial $1$.
--
--   The coefficient mass is $2\sum_j|a_j|$. Exactification keeps the prefix, erases the component allowed at the next parity, and erases the other component on the following step. Feasibility of these operations is asserted separately, rather than built into the operation.
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), §2.2, (1)–(2); Lemma 4.11 proof, p.6–7, 22 (PDF p.6–7, 22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Mathlib

open scoped BigOperators

namespace OrderedSearchExact.Exact

/-- Frequency i means j=i+1. Fin.rev is exactly j ↦ n-j. -/
abbrev Coeff (n : ℕ) := Fin (n - 1) → ℝ

def reversal {n : ℕ} (a : Coeff n) : Coeff n := fun i => a i.rev

noncomputable def projectPlus {n : ℕ} (a : Coeff n) : Coeff n := (a + reversal a) / 2

noncomputable def projectMinus {n : ℕ} (a : Coeff n) : Coeff n := (a - reversal a) / 2

/-- Normalized real symmetric Laurent polynomial of degree less than n, evaluated at z.
Only nonzero z are used as Laurent arguments. -/
noncomputable def laurent {n : ℕ} (a : Coeff n) (z : ℂ) : ℂ :=
  1 + ∑ i, (a i : ℂ) * (z ^ (i.val + 1) + (z ^ (i.val + 1))⁻¹)

noncomputable def circle {n : ℕ} (a : Coeff n) (θ : ℝ) : ℝ :=
  1 + 2 * ∑ i, a i * Real.cos ((i.val + 1 : ℕ) * θ)

def Nonnegative {n : ℕ} (a : Coeff n) : Prop := ∀ θ : ℝ, 0 ≤ circle a θ

noncomputable def fejer (n : ℕ) : Coeff n := fun i => 1 - (i.val + 1 : ℕ) / (n : ℝ)

/-- t is the one-based query number; odd steps change the + eigenspace. -/
def ParityStep {n : ℕ} (t : ℕ) (a b : Coeff n) : Prop :=
  reversal (b - a) = if Odd t then b - a else -(b - a)

def FeasiblePrefix (n k : ℕ) (p : ℕ → Coeff n) : Prop :=
  p 0 = fejer n ∧
  (∀ t ≤ k, Nonnegative (p t) ∧
    (∫ θ in (0 : ℝ)..(2 * Real.pi), circle (p t) θ) = 2 * Real.pi) ∧
  ∀ t, 1 ≤ t → t ≤ k → ParityStep t (p (t - 1)) (p t)

def FeasiblePath (n k : ℕ) (p : ℕ → Coeff n) : Prop :=
  FeasiblePrefix n k p ∧ p k = 0

noncomputable def mass {n : ℕ} (a : Coeff n) : ℝ := 2 * ∑ i, |a i|

/-- The next allowed component is erased, then the remaining component is erased. -/
noncomputable def exactifierMiddle {n : ℕ} (k : ℕ) (a : Coeff n) : Coeff n :=
  if Odd (k + 1) then projectMinus a else projectPlus a

noncomputable def exactify {n : ℕ} (p : ℕ → Coeff n) (k : ℕ) : ℕ → Coeff n :=
  fun t => if t ≤ k then p t else if t = k + 1 then exactifierMiddle k (p k) else 0

end OrderedSearchExact.Exact


