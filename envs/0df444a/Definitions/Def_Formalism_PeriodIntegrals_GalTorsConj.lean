-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_GalTorsConj
-- name    : Formalism_PeriodIntegrals_GalTorsConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:39.056908+00:00
-- url     : https://prove2.me/theorems/1fd0f96e-4258-4943-8323-c01ed4539766
-- title:
--   Gal Tors Conj
-- statement:
--   Definitions and structural lemmas for Gal Tors Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/GalTorsConj.lean

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
namespace PI.GalTorsConj
open Classical
open scoped Pointwise
def lat2 (w₁ w₂ : ℂ) : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂}
def eisG (Λ : AddSubgroup ℂ) (k : ℕ) : ℂ :=
  ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)
def g2 (Λ : AddSubgroup ℂ) : ℂ := 60 * eisG Λ 2
def g3 (Λ : AddSubgroup ℂ) : ℂ := 140 * eisG Λ 3
def liftM (M : IntermediateField ℚ ℂ) (x : ℂ) : M := if h : x ∈ M then ⟨x, h⟩ else 0
def lamConj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) : AddSubgroup ℂ :=
  Classical.epsilon (fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)))
def cj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : ℂ) : ℂ := ρ (liftM M x)
def wpF (Λ : AddSubgroup ℂ) (z : ℂ) : ℂ :=
  1 / z ^ 2 + ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, (1 / (z - (w : ℂ)) ^ 2 - 1 / (w : ℂ) ^ 2)
def wpD (Λ : AddSubgroup ℂ) (z : ℂ) : ℂ := -2 * ∑' w : Λ, 1 / (z - (w : ℂ)) ^ 3
def StarPt (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) (t t' : ℂ) : Prop :=
  (t ∈ Λ ∧ t' ∈ lamConj M ρ Λ) ∨
  (t ∉ Λ ∧ t' ∉ lamConj M ρ Λ ∧ wpF Λ t ∈ M ∧ wpD Λ t ∈ M ∧
    wpF (lamConj M ρ Λ) t' = cj M ρ (wpF Λ t) ∧ wpD (lamConj M ρ Λ) t' = cj M ρ (wpD Λ t))
def InRationalLattice (Λ : AddSubgroup ℂ) (x : ℂ) : Prop := ∃ m : ℕ, 0 < m ∧ (m : ℂ) * x ∈ Λ
def Clauses (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) : Prop :=
  (∀ t, InRationalLattice Λ t → (t ∈ Λ ∨ (wpF Λ t ∈ M ∧ wpD Λ t ∈ M)) → ∃ t', StarPt M ρ Λ t t') ∧
  (∀ t t₁ t₂, StarPt M ρ Λ t t₁ → (StarPt M ρ Λ t t₂ ↔ t₁ - t₂ ∈ lamConj M ρ Λ)) ∧
  (∀ t t' ω, StarPt M ρ Λ t t' → ω ∈ Λ → StarPt M ρ Λ (t + ω) t') ∧
  (∀ t t' u u', StarPt M ρ Λ t t' → StarPt M ρ Λ u u' → StarPt M ρ Λ (t + u) (t' + u')) ∧
  (∀ c : ℂ, (∀ t ∈ Λ, c * t ∈ Λ) → c ∈ M → cj M ρ c = c →
    ∀ t t', StarPt M ρ Λ t t' → StarPt M ρ Λ (c * t) (c * t')) ∧
  (∀ (n : ℕ) t t', StarPt M ρ Λ t t' → ((n : ℂ) * t ∈ Λ ↔ (n : ℂ) * t' ∈ lamConj M ρ Λ)) ∧
  (∀ n : ℕ, 0 < n →
    (∀ t, (n : ℂ) * t ∈ Λ → t ∉ Λ → wpF Λ t ∈ M ∧ wpD Λ t ∈ M) →
    ∀ t', (n : ℂ) * t' ∈ lamConj M ρ Λ → ∃ t, (n : ℂ) * t ∈ Λ ∧ StarPt M ρ Λ t t')
def Target : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ),
      g2 (lat2 w₁ w₂) ∈ M → g3 (lat2 w₁ w₂) ∈ M → Clauses M ρ (lat2 w₁ w₂)
end PI.GalTorsConj


