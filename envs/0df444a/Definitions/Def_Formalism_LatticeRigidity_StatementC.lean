-- Prove2me | Definitions.Def_Formalism_LatticeRigidity_StatementC
-- name    : Formalism_LatticeRigidity_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:08:21.453454+00:00
-- url     : https://prove2.me/theorems/f62d7dda-67fa-4243-8d09-ef1ffaeee344
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/StatementC.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SA.C
open Finset Real
def RecHyp (r : ℕ) (ε δ M : ℝ) (s m : ℕ → ℝ) : Prop :=
  0 ≤ ε ∧ 0 ≤ δ ∧ s 0 ≤ M ∧ (∀ i, 0 ≤ s i) ∧
  (∀ i, 1 ≤ i → i ≤ r + 1 →
    √(s i) ≤ (1 + ε) * √(s (i-1)) + ∑ t ∈ Icc 2 i, δ ^ (t-1) * √(s (i-t))) ∧
  m 0 = 1 ∧
  (∀ i, 1 ≤ i → i ≤ r + 1 →
    √(m i) ≤ √(m (i-1) + ε * s (i-1)) * (1 + ε) + ∑ t ∈ Icc 2 i, δ ^ (t-1) * √(s (i-t))) ∧
  r * (ε + δ) ≤ 1/10
def RecursionUnrestricted : Prop :=
  ∃ C : ℝ, ∀ (r : ℕ) (ε δ M : ℝ) (s m : ℕ → ℝ), RecHyp r ε δ M s m →
    (∀ i ≤ r + 1, s i ≤ 2 * M) ∧ √(m (r+1)) ≤ 1 + C * r * (ε * M + δ * √M)
def Recursion : Prop :=
  ∃ C : ℝ, ∀ (r : ℕ) (ε δ M : ℝ) (s m : ℕ → ℝ), 1 ≤ r → 1 ≤ M → RecHyp r ε δ M s m →
    (∀ i ≤ r + 1, s i ≤ 2 * M) ∧ √(m (r+1)) ≤ 1 + C * r * (ε * M + δ * √M)
def RecursionSucc : Prop :=
  ∃ C : ℝ, ∀ (r : ℕ) (ε δ M : ℝ) (s m : ℕ → ℝ), 1 ≤ M → ((r : ℝ) + 1) * (ε + δ) ≤ 1/10 →
    RecHyp r ε δ M s m →
    (∀ i ≤ r + 1, s i ≤ 2 * M) ∧ √(m (r+1)) ≤ 1 + C * ((r : ℝ) + 1) * (ε * M + δ * √M)
def RecursionUnrestrictedFalse : Prop := ¬ RecursionUnrestricted
noncomputable def chebPt (α β : ℝ) (n : ℕ) (j : Fin (n+1)) : ℝ :=
  (α + β) / 2 + (β - α) / 2 * Real.cos (π * (j : ℕ) / n)
def ChebLead : Prop :=
  ∀ (α β : ℝ) (n : ℕ), α < β → 1 ≤ n → ∀ y : Fin (n+1) → ℝ,
    (∀ j, |y j - chebPt α β n j| ≤ (β - α) / (10 * (n:ℝ)^2)) →
    ∃ co : Fin (n+1) → ℝ, ∑ j, |co j| ≤ 4 * (4 / (β - α)) ^ n ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (a : Fin (n+1) → V),
        a (Fin.last n) = ∑ j, co j • ∑ k : Fin (n+1), (y j) ^ (k : ℕ) • a k
open NumberField in

def BoxSum : Prop :=
  ∃ C : ℝ, ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), b ≠ 0 →
    ∀ (x : InfinitePlace E → ℝ) (Θ Kx : ℝ), (∀ w, 0 < x w) → 2 < Θ → 3 ≤ Kx →
      Θ ^ Fintype.card (InfinitePlace E) =
        √(FractionalIdeal.absNorm b : ℝ) / ∏ w, x w →
      ∀ S : Finset E, (∀ l ∈ S, l ∈ b ∧ l ≠ 0) →
        ∑ l ∈ S, ∏ w, min 1 ((x w / w l) ^ Kx) ≤
          (C * Θ ^ (-(Kx - 5/2))) ^ Fintype.card (InfinitePlace E)
end Formalism.SA.C


