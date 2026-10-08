-- Prove2me | Definitions.Def_JointDickman
-- name    : JointDickman
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:15.962986+00:00
-- url     : https://prove2.me/theorems/244456e1-4cc0-478d-9d85-adaaeb8beb75
-- statement:
--   This block sets up auxiliary definitions for a joint Dickman law for consecutive integers, and states no theorem. Nat.maxPrimeFac(n) is the last element of the list of prime factors of n, i.e. the largest prime factor, with the upstream defaults maxPrimeFac(0)=0 and maxPrimeFac(1)=1. The Dickman function ρ is built through a delay equation: kernel(f,t)=f(t−1)/max(1,t); stepApprox(σ,n) is a Picard-type iteration starting from the constant function 1, where step n+1 sends u to 1+σ∫ from 1 to max(1,u) of kernel(stepApprox(σ,n),t) dt; delay(σ,u) evaluates the ⌈u⌉-th iterate at u; and ρ is delay with σ=−1. For a predicate P on naturals, empiricalCount(P,N) counts the integers n with 2≤n≤N satisfying P, and realDensity(P,X) is the count up to ⌊X⌋ divided by the real endpoint X. The closing paper namespace only opens filter and topology notation and contains no further definitions or results.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/JointDickman.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/JointDickman.lean; bytes 16..1191
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

-- Faithful backport of Mathlib/Data/Nat/MaxPrimeFac.lean at
-- d13f23b723b8a846827a245b89c10fc7d3f11612 (Lean 4.34.1).
-- Preserve the upstream defaults: maxPrimeFac 0 = 0 and maxPrimeFac 1 = 1.
def Nat.maxPrimeFac (n : ℕ) : ℕ := n.primeFactorsList.getLastD n

namespace OAI

/-! # The joint Dickman law for consecutive integers -/

namespace Erdos970.NumberTheoryLean.DelayConstruction

noncomputable def kernel (f : ℝ → ℝ) (t : ℝ) : ℝ := f (t - 1) / max 1 t

noncomputable def stepApprox (σ : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun u => 1 + σ * ∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t

noncomputable def delay (σ u : ℝ) : ℝ := stepApprox σ ⌈u⌉₊ u

end Erdos970.NumberTheoryLean.DelayConstruction

namespace Erdos970.NumberTheoryLean.Dickman

/-- The continuous delay-equation construction of the Dickman function. -/
noncomputable def rho : ℝ → ℝ := DelayConstruction.delay (-1)

end Erdos970.NumberTheoryLean.Dickman

namespace JointDickman

noncomputable def empiricalCount (P : ℕ → Prop) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 2 N).filter P).card

/-- Ordinary natural density over `2 ≤ n ≤ X`, normalized by the real endpoint. -/
noncomputable def realDensity (P : ℕ → Prop) (X : ℝ) : ℝ :=
  (empiricalCount P ⌊X⌋₊ : ℝ) / X

end JointDickman

namespace JointDickmanPaper

open Filter JointDickman
open scoped Topology



end JointDickmanPaper
end OAI


