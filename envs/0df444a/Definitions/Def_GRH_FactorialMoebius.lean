-- Prove2me | Definitions.Def_GRH_FactorialMoebius
-- name    : GRH_FactorialMoebius
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-27T00:45:02.551429+00:00
-- url     : https://prove2.me/theorems/74439314-a423-5aa3-963f-d54ea1a4e257
-- title:
--   Factorial moduli and one-sided Möbius bounds at square cutoffs
-- statement:
--   Defines the sum of Möbius coefficients coprime to q, a one-sided square-cutoff bound in each unit class, the exact centered estimate at one modulus, and Dirichlet zero-freeness at that level. At index k the sparse criterion uses level (k+2)! and exponent 1/2+1/(k+3). It asks for successes at arbitrarily large indices.
-- source:
--   The target is GRH.centered_moebius_progression_bilinear_power_bound. The earlier square-cutoff reduction and the ordinary modulus-one case are posted on Prove2Me. https://prove2.me/submissions/ee54ee24-4b20-4f98-a25f-5407bc8e90b0

import Definitions.Def_GRH_OneSidedMoebius
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace GRH.FactorialMoebius

open Finset
noncomputable section

def coprimeSum (q : ℕ) [NeZero q] (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0

def principalUpper (q : ℕ) [NeZero q] (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, coprimeSum q n ≤ C * ((n : ℝ) + 1)^θ

def upper (q : ℕ) [NeZero q] (θ : ℝ) : Prop :=
  ∀ a : ZMod q, IsUnit a → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ,
    OneSidedMoebius.residue a (u^2) ≤ C * ((u : ℝ)^2 + 1)^θ

def centered (q : ℕ) [NeZero q] : Prop :=
  ∀ a : ZMod q, IsUnit a → ∀ σ : ℝ, 1/2 < σ → σ < 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |centeredMoebiusBilinear q a n| ≤ C * ((n : ℝ)+1)^σ

def rightHalfPlane (q : ℕ) [NeZero q] : Prop :=
  ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), 1/2 < s.re → ¬ (χ = 1 ∧ s = 1) →
    χ.LFunction s ≠ 0

abbrev level (k : ℕ) := (k+2).factorial

instance (k : ℕ) : NeZero (level k) := ⟨(Nat.factorial_pos _).ne'⟩

def exponent (k : ℕ) : ℝ := 1/2 + 1/((k : ℝ)+3)

def diagonal : Prop := ∀ b : ℕ, ∃ k : ℕ, b ≤ k ∧ upper (level k) (exponent k)

end
end GRH.FactorialMoebius


