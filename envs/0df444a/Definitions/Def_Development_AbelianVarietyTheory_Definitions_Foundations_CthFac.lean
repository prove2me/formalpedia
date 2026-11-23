-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_CthFac
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_CthFac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:00.458497+00:00
-- url     : https://prove2.me/theorems/70ae8024-96b7-4bf7-a0c0-1584567b0807
-- title:
--   Cth Fac
-- statement:
--   Definitions and structural lemmas for Cth Fac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/CthFac.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped UpperHalfPlane MatrixGroups
namespace GlobalTheory.Sieg
def ee (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * z)
def cthFac (c : ℕ) (q t : ℂ) (m : ℕ) : ℂ :=
  (1 - q ^ m * t) ^ (c ^ 2) * (1 - q ^ m * t⁻¹) ^ (c ^ 2) / ((1 - q ^ m * t ^ c) * (1 - q ^ m * (t ^ c)⁻¹))
def cth (c : ℕ) (q t : ℂ) : ℂ :=
  q ^ ((c ^ 2 - 1) / 12) * (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (1 - t) ^ (c ^ 2) / (1 - t ^ c) *
    ∏' m : ℕ, cthFac c q t (m + 1)
def pt (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := (x 0 : ℂ) * (τ : ℂ) + (x 1 : ℂ)
def sg (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := cth c (ee τ) (ee (pt x τ))
open Classical in

def f0 (j : ℕ) (x : Fin 2 → ℚ) : ℂ :=
  if j = 1 then (if Int.fract (x 0) = 0 then (1 / 2) * (1 + ee (x 1)) / (1 - ee (x 1)) else 1 / 2 - ((Int.fract (x 0) : ℚ) : ℂ))
  else -((((Polynomial.bernoulli j).eval (Int.fract (x 0)) : ℚ)) : ℂ) / j
open Classical in

def fTerm (j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) (p : ℤ × ℤ) : ℂ :=
  if 0 < (x 0 + p.1) * p.2 then
    (Int.sign p.2 : ℂ) * ((x 0 + p.1 : ℚ) : ℂ) ^ (j - 1) * ee (((x 0 + p.1 : ℚ) : ℂ) * p.2 * (τ : ℂ)) * ee ((x 1 : ℂ) * p.2)
  else 0
def F (j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := f0 j x + ∑' p : ℤ × ℤ, fTerm j x τ p
def cF (c j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := (c : ℂ) ^ 2 * F j x τ - (c : ℂ) ^ (2 - (j : ℤ)) * F j (c • x) τ
def admitted (c : ℕ) (x : Fin 2 → ℚ) : Prop :=
  1 < c ∧ Nat.Coprime c 6 ∧ ¬ ((c : ℚ) * x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c : ℚ) * x 1 ∈ Set.range ((↑) : ℤ → ℚ))
end GlobalTheory.Sieg


