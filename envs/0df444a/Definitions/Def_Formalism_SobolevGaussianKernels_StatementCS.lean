-- Prove2me | Definitions.Def_Formalism_SobolevGaussianKernels_StatementCS
-- name    : Formalism_SobolevGaussianKernels_StatementCS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:54.043884+00:00
-- url     : https://prove2.me/theorems/5db581a0-ecff-4a64-9925-06363bba7034
-- title:
--   Statement CS
-- statement:
--   Definitions and structural lemmas for Statement CS, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/StatementCS.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SL.CS
open Finset
def KernelBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (P : ι → ι → ℝ) (w : ι → ℂ) (ε₁ ε₂ : ℝ),
    (∀ i j, P i j = P j i) → (∀ i, ‖w i‖ ≤ 1) →
    (∀ i, |(∑ j, P i j) - 1| ≤ ε₁) →
    (∀ i, ‖∑ j, (P i j : ℂ) * w j‖ ≤ ε₂) →
    ‖∑ i, w i‖ ≤ (ε₁ + ε₂) * (Fintype.card ι : ℝ)
def OrbitVanish : Prop :=
  ∀ (G S : Type) [Group G] [Fintype S] [MulAction G S] (f : S → ℂ) (χ : G →* ℂ),
    (∀ g s, f (g • s) = χ g * f s) → (∃ g, χ g ≠ 1) → ∑ s, f s = 0
def PowerSum : Prop :=
  ∀ (p N c : ℕ), p.Prime → 1 ≤ c → c ≤ N →
    ∑ t ∈ range (p ^ N), Complex.exp (2 * Real.pi * Complex.I * ((t : ℂ) / (p : ℂ) ^ c)) = 0
def CharExpandEq : Prop :=
  ∀ (U T : Type) [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (χ : U → ℂ),
    (Fintype.card T : ℂ) * ∑ u ∈ univ.filter (fun u => Q u = 0), χ u
      = ∑ ψ : AddChar T ℂ, ∑ u, ψ (Q u) * χ u
def CharExpand : Prop :=
  ∀ (U T : Type) [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (χ : U → ℂ),
    ∑ u, χ u = 0 →
    ‖∑ u ∈ univ.filter (fun u => Q u = 0), χ u‖ ≤
      (1 / (Fintype.card T : ℝ)) * ∑ ψ ∈ univ.filter (fun ψ : AddChar T ℂ => ψ ≠ 0), ‖∑ u, ψ (Q u) * χ u‖
def SqSum : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (φ : A → ℂ),
    (∀ y, ‖φ y‖ = 1) →
    (∀ d, d ≠ 0 → ∃ (c : ℂ) (χ : AddChar A ℂ), (∃ y, χ y ≠ 1) ∧ ∀ y, φ (y + d) * star (φ y) = c * χ y) →
    ‖∑ y, φ y‖ ^ 2 = (Fintype.card A : ℝ)
def SqSumRad : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (φ : A → ℂ) (K : Finset A),
    (∀ y, ‖φ y‖ = 1) →
    (∀ d, d ∉ K → ∃ (c : ℂ) (χ : AddChar A ℂ), (∃ y, χ y ≠ 1) ∧ ∀ y, φ (y + d) * star (φ y) = c * χ y) →
    ‖∑ y, φ y‖ ^ 2 ≤ (Fintype.card A : ℝ) * (K.card : ℝ)
def KernelBoundRel : Prop :=
  ∀ (ι : Type) [Fintype ι] (P : ι → ι → ℝ) (w : ι → ℂ) (ε₁ ε₂ : ℝ),
    (∀ i j, P i j = P j i) →
    (∀ i, |(∑ j, P i j) - 1| ≤ ε₁) →
    (∀ i, ‖∑ j, (P i j : ℂ) * w j‖ ≤ ε₂ * ‖w i‖) →
    ‖∑ i, w i‖ ≤ (ε₁ + ε₂) * ∑ i, ‖w i‖
end Formalism.SL.CS


