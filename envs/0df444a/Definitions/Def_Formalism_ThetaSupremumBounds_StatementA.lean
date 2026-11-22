-- Prove2me | Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
-- name    : Formalism_ThetaSupremumBounds_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:49:59.989698+00:00
-- url     : https://prove2.me/theorems/467e5afc-f5f4-4366-90e5-8a7be94b63da
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/StatementA.lean

import Mathlib
import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory
open scoped ComplexConjugate Real Nat
noncomputable section
namespace Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
def nsq {κ : Type} [Fintype κ] (u : κ → ℂ) : ℝ := ∑ x, ‖u x‖ ^ 2
def mono {κ : Type} [Fintype κ] (u : κ → ℂ) (e : κ → ℕ) : ℂ := ∏ x, u x ^ e x
def mfact {κ : Type} [Fintype κ] (e : κ → ℕ) : ℕ := ∏ x, (e x)!
def cj {κ : Type} (u : κ → ℂ) : κ → ℂ := fun x => conj (u x)
def SupShift : Prop :=
  ∀ y e s : ℝ, 0 ≤ y → 0 < e → e < 1 → 0 ≤ s →
    s ^ y * Real.exp (-((1 - e) * s ^ 2) / 2) ≤ (1 - e) ^ (-(y / 2)) * Real.exp (ph y / 2)
def EChoice : Prop :=
  ∀ n : ℝ, 0 ≤ n → (1 - 1 / (n + 1)) ^ (-(n / 2)) ≤ Real.exp (1 / 2)
def GaussCoord : Prop :=
  ∀ (κ : Type) [Fintype κ] (b : κ → ℝ), (∀ x, 0 < b x) →
    Integrable (fun u : κ → ℂ => Real.exp (-∑ x, b x * ‖u x‖ ^ 2)) ∧
    ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2) = ∏ x, π / b x
def SingularIntegral : Prop :=
  ∀ (ι : Type) [Fintype ι] (r : ℕ) (ν : Fin r → ℝ) (s : (ι → ℂ) → Fin r → ℝ),
    (∀ i, 0 ≤ ν i) → (∀ i, Measurable fun u => s u i) → (∀ u i, 0 ≤ s u i) →
    (∀ u, ∑ i, s u i ^ 2 = nsq u) →
    Integrable (fun u : ι → ℂ => (∏ i, s u i ^ ν i) * Real.exp (-(nsq u) / 2)) ∧
    (∫ u : ι → ℂ, (∏ i, s u i ^ ν i) * Real.exp (-(nsq u) / 2)) / π ^ Fintype.card ι ≤
      Real.exp (1 / 2) * (2 * (∑ i, ν i) + 2) ^ Fintype.card ι * Real.exp ((∑ i, ph (ν i)) / 2)
def FockJet : Prop :=
  ∀ (κ : Type) [Fintype κ] (F : (κ → ℂ) → ℂ) (c : (κ → ℕ) → ℂ) (S : ℝ),
    Continuous F → (∀ u, HasSum (fun e => c e * mono u e) (F u)) →
    (∀ u, ‖F u‖ ≤ S * Real.exp (nsq u / 2)) →
    ∀ e : κ → ℕ,
      Integrable (fun u : κ → ℂ => F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) ∧
      ∫ u : κ → ℂ, F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ) =
        (π : ℂ) ^ Fintype.card κ * (c e * (mfact e : ℂ))
def BlockIntegral : Prop :=
  ∀ (Pl ι : Type) [Fintype Pl] [Fintype ι] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    (r : ℕ) (ν : Pl → Fin r → ℝ) (s : Pl → (ι → ℂ) → Fin r → ℝ)
    (Th : (Pl × ι → ℂ) → ℂ) (R : (Pl × ι → ℂ) → W) (S : ℝ),
    (∀ τ i, 0 ≤ ν τ i) → (∀ τ u i, 0 ≤ s τ u i) → (∀ τ u, ∑ i, s τ u i ^ 2 = nsq u) →
    (∀ u, ‖Th u‖ ≤ S * Real.exp (nsq u / 2)) →
    (∀ u, ‖R u‖ ≤ ∏ τ, ∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i) →
    ‖∫ u : Pl × ι → ℂ, (Th u * (Real.exp (-(nsq u)) : ℂ)) • R u‖ /
        π ^ (Fintype.card Pl * Fintype.card ι) ≤
      S * ∏ τ, (Real.exp (1 / 2) * (2 * (∑ i, ν τ i) + 2) ^ Fintype.card ι *
        Real.exp ((∑ i, ph (ν τ i)) / 2))
def BlockBound : Prop :=
  ∀ (Pl ι : Type) [Fintype Pl] [Fintype ι] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    [CompleteSpace W]
    (r : ℕ) (ν : Pl → Fin r → ℝ) (n : Pl → ℕ) (s : Pl → (ι → ℂ) → Fin r → ℝ)
    (Th : (Pl × ι → ℂ) → ℂ) (c : (Pl × ι → ℕ) → ℂ) (Rc : (Pl × ι → ℕ) →₀ W)
    (lam : Pl → ℂ) (Om : Pl → ℝ) (S : ℝ),
    (∀ τ i, 0 ≤ ν τ i) → (∀ τ, ∑ i, ν τ i = n τ) →
    (∀ τ u i, 0 ≤ s τ u i) → (∀ τ u, ∑ i, s τ u i ^ 2 = nsq u) →
    Continuous Th → (∀ u, HasSum (fun e => c e * mono u e) (Th u)) →
    (∀ u, ‖Th u‖ ≤ S * Real.exp (nsq u / 2)) →
    (∀ e ∈ Rc.support, ∀ τ, ∑ x, e (τ, x) = n τ) →
    (∀ u, ‖Rc.sum (fun e A => mono (cj u) e • A)‖ ≤ ∏ τ, ∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i) →
    (∀ τ, 0 < Om τ) → (∀ τ, ‖lam τ‖ ^ 2 = (Om τ)⁻¹) →
    ‖Rc.sum (fun e A => (c e * (mfact e : ℂ) * ∏ x, lam x.1 ^ e x) • A)‖ ^ 2 ≤
      S ^ 2 * ∏ τ, ((Om τ)⁻¹ ^ n τ *
        (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) * Real.exp (∑ i, ph (ν τ i))))
def KernelSup : Prop :=
  ∀ (κ Rt : Type) [Fintype κ] [Fintype Rt] (t : Rt → κ → ℂ) (cf : Rt → ℂ) (ka : ℂ)
    (Th0 Th : (κ → ℂ) → ℂ) (B : ℝ), 0 ≤ B →
    (∀ z, ‖Th0 z‖ ^ 2 * Real.exp (-(nsq z)) ≤ B ^ 2) →
    (∀ z, Th z = ka * ∑ a, cf a *
      (Complex.exp (-(∑ x, z x * conj (t a x)) - (nsq (t a) : ℂ) / 2) * Th0 (z + t a))) →
    ∀ z, ‖Th z‖ ≤ ‖ka‖ * (∑ a, ‖cf a‖) * B * Real.exp (nsq z / 2)
def GaussSubmean : Prop :=
  ∀ (κ : Type) [Fintype κ] (F : (κ → ℂ) → ℂ) (c : (κ → ℕ) → ℂ),
    Continuous F → (∀ u, HasSum (fun e => c e * mono u e) (F u)) →
    Integrable (fun w : κ → ℂ => ‖F w‖ ^ 2 * Real.exp (-(2 * nsq w))) →
    ‖F 0‖ ^ 2 ≤ 2 ^ Fintype.card κ *
      ((∫ w : κ → ℂ, ‖F w‖ ^ 2 * Real.exp (-(2 * nsq w))) / π ^ Fintype.card κ)
def ThetaSup : Prop :=
  ∀ (κ : Type) [Fintype κ] (La : AddSubgroup (κ → ℂ)) [Countable La] (D : Set (κ → ℂ))
    (al : La → ℂ) (Th : (κ → ℂ) → ℂ) (c : (κ → ℕ) → ℂ) (hmin : ℝ),
    IsAddFundamentalDomain La D (volume : Measure (κ → ℂ)) →
    0 < hmin → (∀ y ∈ La, y ≠ 0 → π * hmin ≤ nsq y) →
    Continuous Th → (∀ u, HasSum (fun e => c e * mono u e) (Th u)) →
    (∀ y : La, ‖al y‖ = 1) →
    (∀ (y : La) (z : κ → ℂ), Th (z + y) =
      al y * Complex.exp ((∑ x, z x * conj ((y : κ → ℂ) x)) + (nsq (y : κ → ℂ) : ℂ) / 2) * Th z) →
    IntegrableOn (fun u : κ → ℂ => ‖Th u‖ ^ 2 * Real.exp (-(nsq u))) D →
    ∀ z, ‖Th z‖ ^ 2 * Real.exp (-(nsq z)) ≤
      4 ^ Fintype.card κ * (2 + 8 * (Fintype.card κ : ℝ) / hmin) ^ Fintype.card κ *
        ((∫ u in D, ‖Th u‖ ^ 2 * Real.exp (-(nsq u))) / π ^ Fintype.card κ)
end Formalism.DimensionVariation


