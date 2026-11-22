-- Prove2me | Definitions.Def_Formalism_Statement
-- name    : Formalism_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:10.483364+00:00
-- url     : https://prove2.me/theorems/7995c5bd-bf34-4432-844c-7cb6bdc9f6a7
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Formalism
open ArithmeticFunction in

def LamF {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℝ :=
  Λ n * (1 + (χ n).re)
def S {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, LamF χ n * (x / n - 1)
def gammaF {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℝ :=
  Real.eulerMascheroniConstant +
    (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
def G {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  S χ x - x * Real.log x + (1 + gammaF χ) * x
instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩
def quadraticCharFour : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
def quadraticCharThree : DirichletCharacter ℂ 3 := (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)
def quadraticCharacterMod7 : DirichletCharacter ℂ 7 := (quadraticChar (ZMod 7)).ringHomComp (Int.castRingHom ℂ)
def LandauStep : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (∀ n : ℕ, (χ n).im = 0) →
  ∀ σ₀ : ℝ, 0 < σ₀ → σ₀ < 1 →
  (∀ σ : ℝ, σ₀ < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) →
  (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → -C * x ^ σ₀ ≤ G χ x) →
  ∀ s : ℂ, σ₀ < s.re → riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction χ s ≠ 0
def LandauStepEps : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (∀ n : ℕ, (χ n).im = 0) →
  ∀ σ₀ : ℝ, 0 ≤ σ₀ → σ₀ < 1 →
  (∀ σ : ℝ, σ₀ < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) →
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → -C * x ^ (σ₀ + ε) ≤ G χ x) →
  ∀ s : ℂ, σ₀ < s.re → riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction χ s ≠ 0
def RHofG {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → -C * x ^ ((1 : ℝ) / 2 + ε) ≤ G χ x) →
  RiemannHypothesis ∧ ∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction χ s ≠ 0
end Formalism


