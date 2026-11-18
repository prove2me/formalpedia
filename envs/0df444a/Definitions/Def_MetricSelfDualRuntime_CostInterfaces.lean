-- Prove2me | Definitions.Def_MetricSelfDualRuntime_CostInterfaces
-- name    : MetricSelfDualRuntime_CostInterfaces
-- status  : Definition
-- author  : @I am wealthy
-- created : 2026-11-17T19:15:57.232181+00:00
-- url     : https://prove2.me/theorems/133e78fe-0845-41d8-91e0-864fed2e888f
-- title:
--   Polynomial charge contracts for finite stack routines
-- statement:
--   For one fixed finite tree-stack routine R realizing a function f, the polynomial cost contract bounds output tree volume plus execution charge by C times the d-th power of one plus input tree volume, with fixed constants C and d. For a dimension-indexed family of coded types, FamilySize supplies one polynomial bound on every encoded value, and UniformPolynomial bounds the actual execution charge of one dimension-uniform routine by a polynomial in the dimension. These are reusable data and cost interfaces for the deterministic algorithms in Lemma12 and Proposition14 of STOC2027 submission #5. They do not postulate an algorithm or a time bound.
-- source:
--   OAI.ThreeMachine.StackCompiler Realizer/Uniform/Coding/Poly published interfaces (Definitions.Def_OAIThreeMachineSched01); STOC2027 #5, Metric Self-Dual Completion, Lemma12 pp.10-11 and Proposition14 p.12, exact uniform-algorithm formalization. The namespace names retain compatibility with read-only completed common runtime interfaces.

import Definitions.Def_OAIThreeMachineSched01

/-! Polynomial charge contracts for fixed and uniformly dimensioned tree-stack routines.
These are the unchanged contracts used by the exact algorithms for STOC 2027 #5.
They impose actual finite-routine charge bounds; they add no computational assumptions. -/
namespace ExactAmpDich.BinaryMachine
open OAI.ThreeMachine.StackCompiler

def LinearRealizer {α β : Type*} [Coding α] [Coding β] {f : α → β}
    (R : Realizer f) : Prop :=
  ∃ C : ℕ, ∀ x, volume (f x)+R.time x ≤ C*(volume x+1)

def PolynomialRealizer {α β : Type*} [Coding α] [Coding β] {f : α → β}
    (R : Realizer f) : Prop :=
  ∃ C d : ℕ, ∀ x, volume (f x)+R.time x ≤ C*(volume x+1)^d

end ExactAmpDich.BinaryMachine

namespace ExactAmpDich.TractProof.GF2Machine
open OAI.ThreeMachine.StackCompiler

def NatPolynomial (f : ℕ → ℕ) : Prop := ∃d,Poly id f d

class FamilySize (α : ℕ → Type*) [∀n,Coding (α n)] where
  bound : ℕ → ℕ
  polynomial : NatPolynomial bound
  bound_correct : ∀n (x : α n),volume x ≤ bound n

def sizeBound (α : ℕ → Type*) [∀n,Coding (α n)] [h : FamilySize α] : ℕ → ℕ := h.bound

theorem sizeBound_correct {α : ℕ → Type*} [∀n,Coding (α n)] [FamilySize α]
    (n : ℕ) (x : α n) : volume x ≤ sizeBound α n := FamilySize.bound_correct n x

theorem sizeBound_polynomial (α : ℕ → Type*) [∀n,Coding (α n)] [h : FamilySize α] :
    NatPolynomial (sizeBound α) := h.polynomial

def UniformPolynomial {α β : ℕ → Type*} [∀n,Coding (α n)] [∀n,Coding (β n)]
    {f : ∀n,α n → β n} (R : Uniform f) : Prop :=
  ∃T : ℕ → ℕ,NatPolynomial T ∧ ∀n x,R.time n x ≤ T n

end ExactAmpDich.TractProof.GF2Machine


