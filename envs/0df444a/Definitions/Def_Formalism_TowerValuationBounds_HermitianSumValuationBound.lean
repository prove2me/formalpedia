-- Prove2me | Definitions.Def_Formalism_TowerValuationBounds_HermitianSumValuationBound
-- name    : Formalism_TowerValuationBounds_HermitianSumValuationBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:32.950368+00:00
-- url     : https://prove2.me/theorems/d0a00448-6e6d-4215-bb3b-ad4f73900002
-- title:
--   Hermitian Sum Valuation Bound
-- statement:
--   Definitions and structural lemmas for Hermitian Sum Valuation Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TowerValuationBounds/HermitianSumValuationBound.lean

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
namespace Formalism.ValuationGridEstimates
open Finset
def LogPowSumIdentity : Prop :=
  ∀ (ι : Type) (s : Finset ι) (ee ff : ι → ℕ) (n l : ℕ), 0 < n → 0 < l →
    ∑ i ∈ s, ee i * ff i = n →
    ∑ i ∈ s, Real.log ((l : ℝ) ^ ff i) / n * ee i = Real.log l
def AbsValuationSumBound : Prop :=
  ∀ (W E : Type) [Fintype E] (lam val δ : W → ℝ) (absx : E → ℝ) (Wx : Finset W) (Bδ : ℝ),
    (∀ w, 0 ≤ lam w) → (∀ w, w ∉ Wx → val w = 0) →
    ∑ w ∈ Wx, lam w * val w = (∑ σ, Real.log (absx σ)) / Fintype.card E →
    (∑ w ∈ Wx, lam w * |val w| =
        (∑ σ, Real.log (absx σ)) / Fintype.card E + 2 * ∑ w ∈ Wx, lam w * max 0 (-val w)) ∧
    (∑ w ∈ Wx, lam w * |val w| ≤
        (∑ σ, Real.posLog (absx σ)) / Fintype.card E + 2 * ∑ w ∈ Wx, lam w * max 0 (-val w)) ∧
    ((∀ w, 0 ≤ δ w) → (∀ w, -(3 * δ w) ≤ val w) → (∀ F : Finset W, ∑ w ∈ F, lam w * δ w ≤ Bδ) →
      ∀ F : Finset W, ∑ w ∈ F, lam w * |val w| ≤
        (∑ σ, Real.posLog (absx σ)) / Fintype.card E + 6 * Bδ)
def TowerProductFormula : Prop :=
  ∀ (K : Type) [Field K] (L : ℤ → K) (c u : ℕ → ℕ → K) (p q : ℕ) (e : ℤ),
    (∀ k : ℕ, 1 ≤ k → k ≤ q → L (e + k) ≠ 0) →
    (∀ j, j < q → c 0 j * L (e + j + 1) = u 0 j * c 0 (j + 1)) →
    (∀ i, i < p → c i q = u i q * L (e - i + q) * c (i + 1) q) →
    c 0 0 = ((∏ j ∈ range q, u 0 j) * ∏ i ∈ range p, u i q) * c p q *
      (∏ k ∈ Icc 1 p, L (e + q - k + 1)) / ∏ k ∈ Icc 1 q, L (e + k)
def TowerProductRatioFormula : Prop :=
  ∀ (K : Type) [Field K] (L L0 : ℤ → K) (c u c0 u0 : ℕ → ℕ → K) (p q : ℕ) (e : ℤ) (Ω Ω' : K),
    Ω ≠ 0 → Ω' ≠ 0 →
    (∀ k : ℕ, 1 ≤ k → k ≤ q → L (e + k) ≠ 0 ∧ L0 (e + k) ≠ 0) →
    (∀ j, j < q → c 0 j * L (e + j + 1) = u 0 j * c 0 (j + 1)) →
    (∀ i, i < p → c i q = u i q * L (e - i + q) * c (i + 1) q) →
    (∀ j, j < q → c0 0 j * L0 (e + j + 1) = u0 0 j * c0 0 (j + 1)) →
    (∀ i, i < p → c0 i q = u0 i q * L0 (e - i + q) * c0 (i + 1) q) →
    c 0 0 / c0 0 0 =
      ((∏ j ∈ range q, u 0 j / u0 0 j) * ∏ i ∈ range p, u i q / u0 i q) *
      ((c p q * Ω' / Ω) / (c0 p q * Ω' / Ω)) *
      (∏ k ∈ Icc 1 p, L (e + q - k + 1) / L0 (e + q - k + 1)) *
      (∏ k ∈ Icc 1 q, L (e + k) / L0 (e + k))⁻¹
def IndexRangeConditions : Prop :=
  ∀ (a a' d h p q e : ℕ), a + a' = d → a = a' + 2 * e → d = 2 * h →
    2 * (p + q) + 1 < e → 2 * (p + q) + 1 < a' →
    (2 * p ≤ a ∧ 2 * q ≤ a' ∧ p ≤ e + q ∧ a - 2 * p = (a' - 2 * q) + 2 * (e + q - p) ∧
      (a - 2 * p) + (a' - 2 * q) = d - 2 * (p + q) ∧ d - 2 * (p + q) = 2 * (h - (p + q))) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ p → (e : ℤ) - p < e + q - k + 1 ∧ (e : ℤ) + q - k + 1 ≤ e + q) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ q → (e : ℤ) - p < e + k ∧ (e : ℤ) + k ≤ e + q ∧ (2 : ℤ) ≤ e + k) ∧
    (∀ s : ℤ, (e : ℤ) - p < s → s ≤ e + q → 1 ≤ s ∧ s ≤ h) ∧
    (∀ s : ℤ, 1 - ((e : ℤ) + q - p) ≤ s → s ≤ (h : ℤ) - (p + q) →
      s ≤ h ∧ ((1 ≤ s ∧ s ≤ h) ∨ (1 ≤ 1 - s ∧ 1 - s ≤ h))) ∧
    (a - 2 * p) + p + q ≤ d
def NormArgumentReindexing : Prop :=
  ∀ (M : Type) [CommMonoid M] (a0 a0' e0 h0 : ℕ), a0 = a0' + 2 * e0 → a0 + a0' = 2 * h0 →
    (∀ L : ℚ → M, ∏ i ∈ range a0, L ((a0' : ℚ) / 2 + (a0 : ℚ) / 2 - i) =
      ∏ s ∈ Icc (1 - (e0 : ℤ)) h0, L (s : ℚ)) ∧
    (∀ L : ℚ → M, ∏ i ∈ range a0', L ((a0 : ℚ) / 2 + (a0' : ℚ) / 2 - i) =
      ∏ s ∈ Icc (1 + (e0 : ℤ)) h0, L (s : ℚ)) ∧
    (∀ Lη : ℕ → ℕ → M, (∀ j k, Lη j (k + 2) = Lη j k) →
      ∏ i ∈ Icc 1 a0, Lη (a0' + i) (2 * h0 + a0 - i) = ∏ j ∈ Ioc a0' (2 * h0), Lη j j) ∧
    (1 ≤ a0' → ∀ j ∈ Ioc a0' (2 * h0), 2 ≤ j)
def NormProductRatio : Prop :=
  ∀ (K : Type) [Field K] (Ac Ω2 : K) (L L0 : ℤ → K) (lo hi : ℤ), Ac ≠ 0 → Ω2 ≠ 0 →
    (Ac * (∏ s ∈ Icc lo hi, L s) / Ω2) / (Ac * (∏ s ∈ Icc lo hi, L0 s) / Ω2) =
      ∏ s ∈ Icc lo hi, L s / L0 s
def LocalIndexIdentity : Prop :=
  ∀ (q : ℝ) (a a' c : ℕ), 1 < q →
    let P : ℕ → ℝ := fun n => ∏ i ∈ Icc 1 n, (1 - (q ^ i)⁻¹)
    let idx : ℝ := q ^ (c * a * a') * P (a + a') / (P a * P a')
    let Z : ℝ := (q ^ (c * a * a'))⁻¹ * P a
    let dv : ℝ := (∏ j ∈ Ioc a' (a + a'), (1 - (q ^ j)⁻¹))⁻¹
    let g : ℕ → ℝ := fun n => ∏ i ∈ range n, (q ^ n - q ^ i)
    dv * idx * Z = 1 ∧
    (1 ≤ c → idx = q ^ ((c - 1) * a * a') * (g (a + a') / (g a * g a' * q ^ (a * a')))) ∧
    Z = g a / q ^ (a * a) * (q ^ (c * a * a'))⁻¹
def HermitianSumValuationBound : Prop :=
  ∀ (K : Type) [Field K] (v vc : AddValuation K (WithTop ℝ)) (conj : K →+* K),
    (∀ x, v (conj x) = vc x) →
    ∀ (ι κ : Type) [Fintype κ] (X : Finset ι) (z z' : ι → κ → K) (gm : ι → κ → κ → K)
      (c0 : K) (δ : ℝ), c0 ≠ 0 →
    (∀ x ∈ X, ∀ k, z x k = c0 * z' x k) →
    (∀ x ∈ X, ∀ k, ((-δ : ℝ) : WithTop ℝ) ≤ v (z x k) ∧ ((-δ : ℝ) : WithTop ℝ) ≤ vc (z x k) ∧
      ((-δ : ℝ) : WithTop ℝ) ≤ v (z' x k) ∧ ((-δ : ℝ) : WithTop ℝ) ≤ vc (z' x k)) →
    (∀ x ∈ X, ∀ k l, ((-δ : ℝ) : WithTop ℝ) ≤ v (gm x k l)) →
    v c0 ≤ v (∑ x ∈ X, ∑ k, ∑ l, z x k * conj (z x l) * gm x k l) + ((3 * δ : ℝ) : WithTop ℝ) ∧
    v c0⁻¹ ≤ v (∑ x ∈ X, ∑ k, ∑ l, z' x k * conj (z' x l) * gm x k l) + ((3 * δ : ℝ) : WithTop ℝ) ∧
    ((-(3 * δ) : ℝ) : WithTop ℝ) ≤ v (∑ x ∈ X, ∑ k, ∑ l, z x k * conj (z x l) * gm x k l) ∧
    ((-(3 * δ) : ℝ) : WithTop ℝ) ≤ v (∑ x ∈ X, ∑ k, ∑ l, z' x k * conj (z' x l) * gm x k l)
def QuotientValuationBound : Prop :=
  ∀ (G : Type) [CommGroup G] (v : G → ℝ), (∀ x y, v (x * y) = v x + v y) →
    ∀ (T Td Tdp ρ : G) (N0 ε : ℝ), ρ = Tdp / T → -N0 ≤ v Tdp → -N0 ≤ v T → v Tdp ≤ v Td + ε →
      v ρ ≤ |v Td| + |v T| + ε ∧ -v ρ ≤ v T + N0 ∧ 0 ≤ v T + N0
def GaussSumTwist : Prop :=
  ∀ (R : Type) [CommRing R] [Fintype R] [DecidableEq R] (I : Ideal R) (ψ : AddChar R ℂ)
    (ν dl : Rˣ →* ℂˣ) (c : R) (x0 : Rˣ),
    (∀ y ∈ I, ∀ y' ∈ I, y * y' = 0) →
    (∀ z : R, (∀ y ∈ I, ψ (z * y) = 1) → z ∈ I) →
    (∀ u : Rˣ, (u : R) - 1 ∈ I → ((ν u : ℂˣ) : ℂ) = ψ (c * ((u : R) - 1))) →
    (∀ u : Rˣ, (u : R) - 1 ∈ I → dl u = 1) →
    (x0 : R) - c ∈ I →
    (∑ x : Rˣ, (((ν x)⁻¹ : ℂˣ) : ℂ) * ψ (x : R) =
      (Nat.card I : ℂ) * ((((ν x0)⁻¹ : ℂˣ) : ℂ) * ψ (x0 : R))) ∧
    (∑ x : Rˣ, ((((ν * dl) x)⁻¹ : ℂˣ) : ℂ) * ψ (x : R) =
      (((dl x0)⁻¹ : ℂˣ) : ℂ) * ∑ x : Rˣ, (((ν x)⁻¹ : ℂˣ) : ℂ) * ψ (x : R))
def UnitQuotientValuationBound : Prop :=
  ∀ (G : Type) [CommGroup G] (v : G → ℝ), (∀ x y, v (x * y) = v x + v y) →
    ∀ (S : Type) (S0 : Finset S) (ζ : G) (Ga Ga' Gb Gb' qv : S → G) (c : S → ℕ), v ζ = 0 →
    (∀ s ∈ S0, 0 ≤ v (Ga s) ∧ 0 ≤ v (Ga' s) ∧ Ga s * Ga' s = qv s ^ c s) →
    (∀ s ∈ S0, 0 ≤ v (Gb s) ∧ 0 ≤ v (Gb' s) ∧ Gb s * Gb' s = qv s ^ c s) →
    |v (ζ * ∏ s ∈ S0, Ga s / Gb s)| ≤ ∑ s ∈ S0, (c s : ℝ) * v (qv s) ∧
    |v (ζ * ∏ s ∈ S0, Ga s / Gb s)| ≤ ∑ s ∈ S0, 2 * (c s : ℝ) * v (qv s)
def TowerValuationBound : Prop :=
  ∀ (G : Type) [CommGroup G] (v : G → ℝ), (∀ x y, v (x * y) = v x + v y) →
    ∀ (a a' d h p q e : ℕ), a + a' = d → a = a' + 2 * e → d = 2 * h →
    2 * (p + q) + 1 < e → 2 * (p + q) + 1 < a' →
    ∀ (T Td Tdp ρ E : ℤ → G) (N0 ε δ σ : ℝ), 0 ≤ N0 → 0 ≤ ε →
    (∀ s : ℤ, 1 ≤ s → s ≤ h →
      ρ s = Tdp s / T s ∧ -N0 ≤ v (Tdp s) ∧ v (Tdp s) ≤ v (Td s) + ε) →
    (∀ s : ℤ, 1 - ((e : ℤ) + q - p) ≤ s → s ≤ 0 → ρ s = E s * ρ (1 - s) ∧ v (E s) = 0) →
    ∀ (c0 c00 A A0 A0' : G), v c0 ≤ v A + 3 * δ → -v c00 ≤ v A0' + 3 * δ →
    A / A0 = ∏ s ∈ Icc (1 - ((e : ℤ) + q - p)) ((h : ℤ) - (p + q)), ρ s →
    ∀ (ub ua : ℕ → G), (∀ j, j < q → v (ub j) ≤ σ) → (∀ i, i < p → v (ua i) ≤ σ) →
    ∀ r : G, r = ((∏ j ∈ range q, ub j) * ∏ i ∈ range p, ua i) * (c0 / c00) *
        (∏ k ∈ Icc 1 p, ρ ((e : ℤ) + q - k + 1)) * (∏ k ∈ Icc 1 q, ρ ((e : ℤ) + k))⁻¹ →
    v r ≤ |v A0| + |v A0'| + 4 * (∑ s ∈ Icc (1 : ℤ) h, (|v (T s)| + |v (Td s)|)) +
      d * (N0 + ε) + 6 * δ + (p + q : ℕ) * σ
def TowerValuationBoundSharp : Prop :=
  ∀ (G : Type) [CommGroup G] (v : G → ℝ), (∀ x y, v (x * y) = v x + v y) →
    ∀ (a a' d h p q e : ℕ), a + a' = d → a = a' + 2 * e → d = 2 * h →
    2 * (p + q) + 1 < e → 2 * (p + q) + 1 < a' →
    ∀ (T Td Tdp ρ E : ℤ → G) (N0 ε δ σ : ℝ),
    (∀ s : ℤ, 1 ≤ s → s ≤ h →
      ρ s = Tdp s / T s ∧ -N0 ≤ v (Tdp s) ∧ v (Tdp s) ≤ v (Td s) + ε) →
    (∀ s : ℤ, 1 - ((e : ℤ) + q - p) ≤ s → s ≤ 0 → ρ s = E s * ρ (1 - s) ∧ v (E s) = 0) →
    ∀ (c0 c00 A A0 A0' : G), v c0 ≤ v A + 3 * δ → -v c00 ≤ v A0' + 3 * δ →
    A / A0 = ∏ s ∈ Icc (1 - ((e : ℤ) + q - p)) ((h : ℤ) - (p + q)), ρ s →
    ∀ (ub ua : ℕ → G), (∀ j, j < q → v (ub j) ≤ σ) → (∀ i, i < p → v (ua i) ≤ σ) →
    ∀ r : G, r = ((∏ j ∈ range q, ub j) * ∏ i ∈ range p, ua i) * (c0 / c00) *
        (∏ k ∈ Icc 1 p, ρ ((e : ℤ) + q - k + 1)) * (∏ k ∈ Icc 1 q, ρ ((e : ℤ) + k))⁻¹ →
    v r ≤ v A0 + v A0' + 3 * (∑ s ∈ Icc (1 : ℤ) h, |v (T s)|) + 2 * (∑ s ∈ Icc (1 : ℤ) h, |v (Td s)|) +
      ((a : ℝ) - p) * ε + q * N0 + 6 * δ + (p + q : ℕ) * σ
def PrimeLogSquareSumLtOne : Prop :=
  ∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) → ∑ l ∈ P, Real.log l / (l : ℝ) ^ 2 < 1
def PrimeLogBudget : Prop :=
  ∀ (N0 : ℕ → ℝ) (BN0 : ℝ),
    (∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) → ∑ l ∈ P, N0 l * Real.log l ≤ BN0) →
    ∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) →
      ∑ l ∈ P, (N0 l + ((l : ℝ) ^ 2)⁻¹) * Real.log l ≤ BN0 + 1
def GridValuationBound : Prop :=
  ∀ (W X S : Type) (m N : ℕ) (lam δ : W → ℝ) (ell : W → ℕ) (N0 : ℕ → ℝ)
    (vr : W → Fin m × Fin m → ℝ) (vx : W → X → ℝ) (XX : Fin m × Fin m → Bool → Finset X)
    (ch : W → Bool) (dd yy : Fin m × Fin m → ℕ) (S0 : Finset S) (cc ee qq : S → ℕ)
    (vq : W → S → ℝ) (H : X → ℝ) (B BN Bδ : ℝ) (W0 : Finset W),
    (∀ w, 0 ≤ lam w) → (∀ w, 0 ≤ δ w) → (∀ l, 0 ≤ N0 l) → (∀ w s, 0 ≤ vq w s) →
    (∀ w, (ell w).Prime) →
    (∀ (l : ℕ) (F : Finset W), (∀ w ∈ F, ell w = l) → ∑ w ∈ F, lam w ≤ Real.log l) →
    (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) → (∀ s ∈ S0, cc s ≤ ee s) →
    (∀ w ∈ W0, ∀ ij, vr w ij ≤ (∑ x ∈ XX ij (ch w), |vx w x|) +
      dd ij * (N0 (ell w) + ((ell w : ℝ) ^ 2)⁻¹) + 6 * δ w +
      2 * yy ij * (∑ s ∈ S0, (cc s : ℝ) * vq w s)) →
    (∀ (x : X) (F : Finset W), ∑ w ∈ F, lam w * |vx w x| ≤ H x) →
    (∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) →
      ∑ l ∈ P, (N0 l + ((l : ℝ) ^ 2)⁻¹) * Real.log l ≤ BN) →
    (∀ F : Finset W, ∑ w ∈ F, lam w * δ w ≤ Bδ) →
    (∀ s ∈ S0, ∀ F : Finset W, ∑ w ∈ F, lam w * vq w s ≤ Real.log (qq s)) →
    (∑ w ∈ W0, lam w * ∑ ij, vr w ij ≤
      (∑ ij, ∑ b, ∑ x ∈ XX ij b, H x) +
      (m : ℝ) ^ 2 * (2 * N * BN + 6 * Bδ + 4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))) ∧
    (0 ≤ B → (∀ x, H x ≤ B) → (∀ ij b, (XX ij b).card ≤ 2 + 8 * N) →
      ∑ w ∈ W0, lam w * ∑ ij, vr w ij ≤
        (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B + 2 * N * BN + 6 * Bδ +
          4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) ∧
      ∑ w ∈ W0, lam w * ((∑ ij, vr w ij) + δ w) ≤
        (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B + 2 * N * BN + 6 * Bδ +
          4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) + Bδ)
def GridValuationBoundSquares : Prop :=
  ∀ (W S : Type) (m N : ℕ) (lam δ : W → ℝ) (ell : W → ℕ) (N0 : ℕ → ℝ)
    (vr vA vA' : W → Fin m × Fin m → ℝ) (vT : W → Fin m × Fin m → ℤ → ℝ)
    (vTd : W → Fin m × Fin m → Bool → ℤ → ℝ)
    (ch : W → Bool) (dd hh yy : Fin m × Fin m → ℕ) (S0 : Finset S) (cc ee qq : S → ℕ)
    (vq : W → S → ℝ) (B BN Bδ : ℝ) (W0 : Finset W),
    (∀ w, 0 ≤ lam w) → (∀ w, 0 ≤ δ w) → (∀ l, 0 ≤ N0 l) → (∀ w s, 0 ≤ vq w s) →
    (∀ w, (ell w).Prime) →
    (∀ (l : ℕ) (F : Finset W), (∀ w ∈ F, ell w = l) → ∑ w ∈ F, lam w ≤ Real.log l) →
    (∀ ij, dd ij = 2 * hh ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) →
    (∀ s ∈ S0, cc s ≤ ee s) →
    (∀ w ∈ W0, ∀ ij, vr w ij ≤ |vA w ij| + |vA' w ij| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|vT w ij s| + |vTd w ij (ch w) s|)) +
      dd ij * (N0 (ell w) + ((ell w : ℝ) ^ 2)⁻¹) + 6 * δ w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * vq w s)) →
    (∀ ij (F : Finset W), ∑ w ∈ F, lam w * |vA w ij| ≤ B) →
    (∀ ij (F : Finset W), ∑ w ∈ F, lam w * |vA' w ij| ≤ B) →
    (∀ ij s (F : Finset W), ∑ w ∈ F, lam w * |vT w ij s| ≤ B) →
    (∀ ij b s (F : Finset W), ∑ w ∈ F, lam w * |vTd w ij b s| ≤ B) →
    (∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) →
      ∑ l ∈ P, (N0 l + ((l : ℝ) ^ 2)⁻¹) * Real.log l ≤ BN) →
    (∀ F : Finset W, ∑ w ∈ F, lam w * δ w ≤ Bδ) →
    (∀ s ∈ S0, ∀ F : Finset W, ∑ w ∈ F, lam w * vq w s ≤ Real.log (qq s)) →
    ∑ w ∈ W0, lam w * ∑ ij, vr w ij ≤
      (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B + 2 * N * BN + 6 * Bδ +
        4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))
end Formalism.ValuationGridEstimates


