-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
-- name    : GroundTheory_HeightsAndTheta_Heights_KernelsRest
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:47.412864+00:00
-- url     : https://prove2.me/theorems/90c0af45-2e11-4dde-acae-98e01a0394ef
-- title:
--   Kernels Rest
-- statement:
--   Definitions and structural lemmas for Kernels Rest, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KernelsRest.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Matrix Real
noncomputable section
def alternant {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) : MvPolynomial ι ℚ :=
  (Matrix.of fun i i' : ι => (X i : MvPolynomial ι ℚ) ^ e i').det
def antisym {ι : Type*} [Fintype ι] [DecidableEq ι] (H : MvPolynomial ι ℚ) : MvPolynomial ι ℚ :=
  ∑ w : Equiv.Perm ι, ((Equiv.Perm.sign w : ℤ) : ℚ) • rename w H
def frobDim {r : ℕ} (la : Fin r → ℕ) : ℚ :=
  ((∑ a, la a).factorial : ℚ) *
      (∏ a : Fin r, ∏ b : Fin r,
        if a < b then ((la a + (r - 1 - a) : ℕ) : ℚ) - ((la b + (r - 1 - b) : ℕ) : ℚ) else 1) /
    ∏ a : Fin r, ((la a + (r - 1 - a)).factorial : ℚ)
def AlternantRowRule.Statement : Prop :=
  ∀ (r q : ℕ) (μ : Fin r → ℕ),
    psum (Fin r) ℚ q * alternant μ = ∑ i, alternant (μ + Pi.single i q)
def AlternantPush.Statement : Prop :=
  ∀ r s : ℕ, ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧ ∀ la : Fin r → ℕ, Antitone la →
    antisym (rename Sum.inl (alternant fun a : Fin r => la a + (r - 1 - a)) *
        rename Sum.inr (alternant fun b : Fin s => s - 1 - b)) =
      if ∀ a, s ≤ la a then
        (ε * r.factorial * s.factorial) •
          alternant (Sum.elim (fun a : Fin r => la a + (r - 1 - a)) fun b : Fin s => s - 1 - b)
      else 0
def FrobeniusRectangleBound.Statement : Prop :=
  ∀ (r s : ℕ) (ν : Fin r → ℕ), Antitone ν →
    frobDim (fun a => s + ν a) ≤
      ((r * s + ∑ a, ν a).choose (∑ a, ν a) : ℚ) * frobDim (fun _ : Fin r => s) * frobDim ν
abbrev RootPoly (f j k : ℕ) : Type := MvPolynomial (Fin f × (Fin j ⊕ Fin k)) ℝ
variable (f j k : ℕ)
def flagDim : ℕ := f * ((j + k) * (j + k - 1) / 2)
def rootPsum (m : ℕ) (τ : Fin f) : RootPoly f j k := ∑ i, X (τ, i) ^ m
def lieClass (m : ℕ) : Fin f × Bool → RootPoly f j k
  | (τ, false) => ∑ a : Fin j, X (τ, Sum.inl a) ^ m
  | (τ, true) => (-1) ^ m * ∑ b : Fin k, X (τ, Sum.inr b) ^ m
def vandermonde {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) : R :=
  (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det
def smallMu : RootPoly f j k :=
  ∑ τ : Fin f, if k ≤ j then ∑ b : Fin k, X (τ, Sum.inr b) else ∑ a : Fin j, -X (τ, Sum.inl a)
def fibre : RootPoly f j k :=
  ∏ τ : Fin f, if k ≤ j then
      vandermonde (fun b : Fin k => (X (τ, Sum.inr b) : RootPoly f j k)) *
        vandermonde (fun a : Fin j => (X (τ, Sum.inl a) : RootPoly f j k))
    else
      vandermonde (fun a : Fin j => -(X (τ, Sum.inl a) : RootPoly f j k)) *
        vandermonde (fun b : Fin k => (X (τ, Sum.inr b) : RootPoly f j k))
def restInput : RootPoly f j k := smallMu f j k ^ (f * j * k + 1) * fibre f j k
def degreeInput : RootPoly f j k := smallMu f j k ^ (f * j * k) * fibre f j k
structure IsFlagIntegral (I : RootPoly f j k →ₗ[ℝ] ℝ) : Prop where
  kills : ∀ (m : ℕ) (τ : Fin f) (G : RootPoly f j k), 1 ≤ m → m ≤ flagDim f j k →
    G.IsHomogeneous (flagDim f j k - m) → I (rootPsum f j k m τ * G) = 0
  ne_zero : ∃ G : RootPoly f j k, G.IsHomogeneous (flagDim f j k) ∧ I G ≠ 0
def IsPowerSumDecomposition (F : RootPoly f j k) (Q : Fin f → ℕ → RootPoly f j k) : Prop :=
  (∀ τ m, 1 ≤ m → m ≤ j + k → (Q τ m).IsHomogeneous (flagDim f j k + 1 - m)) ∧
    F = ∑ τ : Fin f, ∑ m ∈ Finset.Icc 1 (j + k), rootPsum f j k m τ * Q τ m
def restAt (I : RootPoly f j k →ₗ[ℝ] ℝ) (vol : ℝ) (φ : ℕ → ℕ → Fin f → Fin f × Bool)
    (Q : Fin f → ℕ → RootPoly f j k) (p : ℕ) : ℝ :=
  log p * vol * ∑ τ : Fin f, ∑ m ∈ Finset.Icc 2 (j + k), ∑' n : ℕ,
    (((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (φ p (n + 1) τ) * Q τ m))
def primesAbove (P : Set ℕ) (B₀ : ℝ) : Type := {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}
def RestTerm.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f j k : ℕ), 1 ≤ f → 1 ≤ j → 1 ≤ k →
    ∀ I : RootPoly f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∀ (vol : ℝ), 0 < vol → ∀ (P : Set ℕ), (∀ p ∈ P, p.Prime) →
    ∀ (B₀ : ℝ), 4 * f * ((j + k : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ φ : ℕ → ℕ → Fin f → Fin f × Bool,
      (∃ Q, IsPowerSumDecomposition f j k (restInput f j k) Q) ∧
      ∀ Q, IsPowerSumDecomposition f j k (restInput f j k) Q →
        Summable (fun p : primesAbove P B₀ => restAt f j k I vol φ Q p.1) ∧
        |∑' p : primesAbove P B₀, restAt f j k I vol φ Q p.1| ≤
          C * (min j k : ℕ) * ((f * j * k : ℕ) + 1) * vol * |I (degreeInput f j k)|
def RestTermSharp.Statement : Prop :=
  ∀ (f j k : ℕ), 1 ≤ f → 1 ≤ j → 1 ≤ k →
    ∀ I : RootPoly f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∀ (vol : ℝ), 0 < vol → ∀ (P : Set ℕ), (∀ p ∈ P, p.Prime) →
    ∀ (B₀ : ℝ), 4 * f * ((j + k : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ φ : ℕ → ℕ → Fin f → Fin f × Bool,
      (∃ Q, IsPowerSumDecomposition f j k (restInput f j k) Q) ∧
      ∀ Q, IsPowerSumDecomposition f j k (restInput f j k) Q →
        Summable (fun p : primesAbove P B₀ => restAt f j k I vol φ Q p.1) ∧
        |∑' p : primesAbove P B₀, restAt f j k I vol φ Q p.1| ≤
          1.6 * ((f * j * k : ℕ) + 1) * vol * |I (degreeInput f j k)|
def flagIntegralOne : RootPoly 1 1 1 →ₗ[ℝ] ℝ :=
  lcoeff ℝ (Finsupp.single (0, Sum.inl 0) 1) - lcoeff ℝ (Finsupp.single (0, Sum.inr 0) 1)
example : (0 : ℝ) < 1 ∧ (∀ p ∈ {p : ℕ | p.Prime}, p.Prime) ∧
    4 * (1 : ℕ) * ((1 + 1 : ℕ) : ℝ) ^ 2 ≤ 16 :=
  ⟨one_pos, fun _ h => h, by norm_num⟩
example : Antitone (![2, 1] : Fin 2 → ℕ) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all
end
end GroundTheory.Heights₂.Heights


