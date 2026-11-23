-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_ContentDistanceBounds
-- name    : Formalism_PieriBlockIdeals_ContentDistanceBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:00.495801+00:00
-- url     : https://prove2.me/theorems/e2f51923-484c-4deb-84dc-44d859dd9da2
-- title:
--   Content Distance Bounds
-- statement:
--   Definitions and structural lemmas for Content Distance Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/ContentDistanceBounds.lean

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent
open Classical
def MinStep : Prop :=
  ∀ (R : Type) [CommRing R] (Q : Type) [AddCommGroup Q] [Module R Q] (l : R) (a b : ℕ),
    (∀ q : Q, l ^ a • q = 0) → (∀ q : Q, l ^ b • q = 0) → ∀ q : Q, l ^ (min a b) • q = 0
def ExactStep : Prop :=
  ∀ (R : Type) [CommRing R] (A B Q : Type) [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup Q] [Module R Q] (f : A →ₗ[R] B) (g : B →ₗ[R] Q) (l : R) (c : ℕ),
    Function.Exact f g → (∀ q : Q, l ^ c • q = 0) → ∀ y : B, l ^ c • y ∈ LinearMap.range f
def ContentDistanceBounds : Prop :=
  ∀ (r w H : ℕ) (lam tau : ℕ → ℕ), Antitone lam → Antitone tau → (∀ a, lam a ≤ tau a) →
    lam 0 ≤ w → w ≤ H → 0 < r → (∀ a < r, ¬ (lam a ≤ a + w ∧ a + w < tau a)) →
    ∀ a < r, ∀ col : ℕ, lam a ≤ col → col < tau a →
      1 ≤ (w : ℤ) - ((col : ℤ) - (a : ℤ)) ∧ (w : ℤ) - ((col : ℤ) - (a : ℤ)) ≤ (H : ℤ) + r - 1
def Markov : Prop :=
  ∀ (k i d : ℕ) (n : Fin k → ℕ), ∑ R, n R ≤ i → 1 ≤ d →
    ((Finset.univ.filter (fun R => d ≤ n R)).card) * d ≤ i
def NoResidue : Prop :=
  ∀ (l : ℕ) (b : ℤ) (t κ : ℕ) (U : Finset ℤ),
    (∀ u ∈ U, u ∉ Finset.Icc b (b + t - 1) → ∀ x ∈ Finset.Icc (b - κ) (b + t - 1 + κ),
      (0 < |u - x| ∧ |u - x| < (l : ℤ)) ∨ ¬ ((l : ℤ) ∣ u - x)) →
    mwCount l b t κ U = 0
def PrimeCount : Prop :=
  ∀ (L : ℝ) (T : Finset ℤ) (P : Finset ℕ), 0 ≤ L → (∀ n ∈ T, n ≠ 0 ∧ ((|n| : ℤ) : ℝ) < L ^ 2) →
    (∀ l ∈ P, l.Prime ∧ L < (l : ℝ) ∧ ∃ n ∈ T, (l : ℤ) ∣ n) → P.card ≤ T.card
def ISum : Prop :=
  ∀ (h : ℕ) (L : ℝ) (xm xp mB : ℤ) (P : Finset ℕ), 0 ≤ L → (h : ℝ) < L ^ 2 → 0 ≤ mB → mB < xm →
    xm ≤ xp → xp ≤ (h : ℤ) → (∀ l ∈ P, l.Prime ∧ L < (l : ℝ)) →
    ∑ l ∈ P, IlInd l xm xp mB * Real.log (l : ℝ) ≤ (((xp - xm : ℤ) : ℝ) + 1) * Real.log (h : ℝ)
def GatedCap : Prop :=
  ∀ (D h : ℕ) (L A k : ℝ) (P : Finset ℕ), 1 ≤ D → D ≤ h → 0 ≤ A → 0 ≤ k → (h : ℝ) < L ^ 2 →
    1 ≤ L → (∀ l ∈ P, l.Prime ∧ L < (l : ℝ)) →
    ∑ l ∈ P, (if ((d0 l D : ℕ) : ℤ) < (D : ℤ) then min k (A / (d0 l D : ℝ)) else 0) *
        Real.log (l : ℝ) ≤
      Real.log (h : ℝ) * ∑ d ∈ Finset.Icc 1 h, min k (A / (d : ℝ))
def SL2CommutationRelation : Prop :=
  ∀ (A : Type) [Ring A] (h e f : A), h * e - e * h = 2 * e → h * f - f * h = -(2 * f) →
    e * f - f * e = h →
    ∀ i : ℕ, e * f ^ (i + 1) - f ^ (i + 1) * e = ((i : A) + 1) * (f ^ i * (h - (i : A)))
end Formalism.CohomologicalDescent


