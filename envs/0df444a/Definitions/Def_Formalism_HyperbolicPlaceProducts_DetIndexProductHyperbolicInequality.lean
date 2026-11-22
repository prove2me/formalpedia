-- Prove2me | Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
-- name    : Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:05:33.28795+00:00
-- url     : https://prove2.me/theorems/8b37fc1a-7810-4645-9d1d-b1cb48826991
-- title:
--   Det Index Product Hyperbolic Inequality
-- statement:
--   Definitions and structural lemmas for Det Index Product Hyperbolic Inequality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/DetIndexProductHyperbolicInequality.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
namespace Formalism.SLP.GlobalBoundRefinements
def J : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def Polarise : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
    (∀ x y, h y x = (starRingEnd ℂ) (h x y)) →
    ∀ y A y' A' : V, y - A = y' + A' → h y A = 0 → h y' A' = 0 →
      h y y + h A A = h y' y' + h A' A'
def EntriesOfSignaturePreserving : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), M.conjTranspose * J * M = J →
    ‖M 0 0‖ = ‖M 1 1‖ ∧ ‖M 0 1‖ = ‖M 1 0‖ ∧ ‖M 0 0‖ ^ 2 - ‖M 1 0‖ ^ 2 = 1 ∧
    ∀ sh ch : ℝ, 0 < sh → 0 ≤ ch → ch ^ 2 = sh ^ 2 + 1 → ‖M 1 0‖ = 1 / sh → ‖M 0 0‖ = ch / sh
def AlHyp : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (sh ch : ℝ) (u u' : ℂ), M.conjTranspose * J * M = J →
    0 < sh → 0 ≤ ch → ch ^ 2 = sh ^ 2 + 1 → ‖M 1 0‖ = 1 / sh → ‖u‖ = ‖u'‖ →
    ‖M 0 0 * u + M 0 1 * u'‖ ≤ ‖u‖ * (1 + ch) / sh
def ProdPlacesHyperbolicInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] (T al n ch sh : ι → ℝ) (Nr : ℝ),
    (∀ v, 0 < T v) → (∀ v, 0 ≤ al v) → (∀ v, 0 < sh v) → (∀ v, 0 ≤ ch v) →
    (∀ v, Real.sqrt (T v) * al v ≤ n v * (1 + ch v) / sh v) → 0 < Nr →
    1 ≤ (∏ v, al v ^ 2) * Nr →
    (∏ v, T v) / Nr ≤ (∏ v, n v ^ 2) * ∏ v, ((1 + ch v) / sh v) ^ 2
def DetIndexProductHyperbolicInequality : Prop :=
  ∀ (detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT K₁ K₂ Nr₁ Nr₂ : ℝ) (e f : ℕ),
    0 < P₁ → 0 < P₂ → 0 < dQ₁ → 0 < dQ₂ → 0 < g → 0 ≤ i₁ → 0 ≤ i₂ → 0 ≤ dLa₁ → 0 ≤ dLa₂ →
    0 < NT → 0 < K₁ → 0 < K₂ → 0 < Nr₁ → 0 < Nr₂ →
    detM = dLa₁ / dPs₁ → detM = dLa₂ / dPs₂ → dPs₁ = P₁ * dQ₁ → dPs₂ = P₂ * dQ₂ →
    dLa₁ * i₁ ^ 2 ≤ G0₁ / Nr₁ → dLa₂ * i₂ ^ 2 ≤ G0₂ / Nr₂ →
    NT / (Nr₂ * K₂ ^ 2) ≤ P₁ → NT / (Nr₁ * K₁ ^ 2) ≤ P₂ →
    g ^ (2 * f * e) ≤ 4 ^ (e * f) * dQ₁ * dQ₂ →
    detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT
def FormCoeff : Prop :=
  ∀ (a b c d : ℂ) (T T' : ℝ), 0 < T → 0 < T' →
    (∀ u v : ℂ, T * ‖a * u + b * v‖ ^ 2 - T' * ‖c * u + d * v‖ ^ 2 = T * ‖u‖ ^ 2 - T' * ‖v‖ ^ 2) →
    ‖a‖ ^ 2 - 1 = T' * ‖c‖ ^ 2 / T ∧ ‖d‖ ^ 2 - 1 = T * ‖b‖ ^ 2 / T' ∧
      (‖a‖ = 1 → c = 0 ∧ b = 0 ∧ ‖d‖ = 1)
def RootUnityTriv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (α : NumberField.RingOfIntegers E)
    (P : Ideal (NumberField.RingOfIntegers E)), P.IsPrime →
    (∀ w : NumberField.InfinitePlace E, w (α : E) = 1) → α - 1 ∈ P →
    ((Nat.card (NumberField.Units.torsion E) : ℕ) : NumberField.RingOfIntegers E) ∉ P → α = 1
def RootUnityModT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (α : NumberField.RingOfIntegers E) (T : ℕ), 3 ≤ T →
    (∀ w : NumberField.InfinitePlace E, w (α : E) = 1) →
    (∃ β : NumberField.RingOfIntegers E, α - 1 = (T : NumberField.RingOfIntegers E) * β) → α = 1
def ThmBEntry : Prop :=
  ∀ (M N : Matrix (Fin 2) (Fin 2) ℂ) (sh₁ ch₁ sh₂ ch₂ : ℝ),
    M.conjTranspose * J * M = J → N.conjTranspose * J * N = J →
    0 < sh₁ → 0 ≤ ch₁ → ch₁ ^ 2 = sh₁ ^ 2 + 1 → 0 < sh₂ → 0 ≤ ch₂ → ch₂ ^ 2 = sh₂ ^ 2 + 1 →
    ‖N 1 0‖ = 1 / sh₁ → ‖M 1 0‖ = 1 / sh₂ →
    ‖(M * N⁻¹) 1 0‖ ≤ (ch₁ + ch₂) / (sh₁ * sh₂)
def SEntry : Prop :=
  ∀ (ga : Matrix (Fin 2) (Fin 2) ℂ) (T T' : ℝ), 0 < T → 0 < T' →
    ‖((Matrix.diagonal ![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)]) * ga *
        (Matrix.diagonal ![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)])⁻¹) 1 0‖ ^ 2 =
      T' * ‖ga 1 0‖ ^ 2 / T
def ThmBNorm : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (s q : F) (x : NumberField.InfinitePlace F → ℝ),
    s ≠ 0 → q ≠ 0 → (∃ β : NumberField.RingOfIntegers F, (β : F) = s / q) →
    (∀ w, w s ≤ x w ^ 2) →
    ∏ w : NumberField.InfinitePlace F, w q ^ w.mult ≤ ∏ w, (x w ^ 2) ^ w.mult
def AutCount : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (e : ℕ) (v : Fin e → M),
    Submodule.span R (Set.range v) = ⊤ → Nat.card (M ≃ₗ[R] M) ≤ Nat.card M ^ e
end Formalism.SLP.GlobalBoundRefinements


