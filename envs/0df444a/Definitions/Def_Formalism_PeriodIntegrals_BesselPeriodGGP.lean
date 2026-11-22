-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
-- name    : Formalism_PeriodIntegrals_BesselPeriodGGP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:02.453814+00:00
-- url     : https://prove2.me/theorems/8813d0e5-27c6-43a0-9cc8-93cad1a8ad5f
-- title:
--   Bessel Period GGP
-- statement:
--   Definitions and structural lemmas for Bessel Period GGP, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/BesselPeriodGGP.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.BesselPeriodGGP
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff ENNReal
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
def lam48 (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Fin (2 * r + k + 1) → ℝ :=
  fun i => if h : i.val < k - 1 then v ⟨i.val, h⟩
    else -b ⟨i.val - (k - 1), by have := i.isLt; omega⟩
def eps48 (k r : ℕ) : Fin (2 * r + k + 1) → Bool :=
  fun i => if i.val < k - 1 then true else decide ((i.val - (k - 1)) % 2 = 0)
def InterlacingCondition (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  (∀ i : Fin (k - 1), v i < u ⟨i.val, by have := i.isLt; omega⟩ ∧
      u ⟨i.val + 1, by have := i.isLt; omega⟩ < v i) ∧
    ∀ h : 0 < k, -b ⟨0, by omega⟩ < u ⟨k - 1, by omega⟩
def HalfIntegralDifference (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ i s, ∃ j : ℤ, u i - lam48 k r v b s = (j : ℝ) + 1 / 2
def rk48 (k r : ℕ) : ℕ := 2 * r + k + 1
def GapBig (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ 1801 ≤ rk48 k r + t ∧
    ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j
def GapC (C : ℝ) (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
    C * (rk48 k r : ℝ) ^ 3 < b ⟨j.val + 1, hj⟩ - b j
def LowGapGe (h : ℝ) (r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2), h ≤ b ⟨j.val + 1, hj⟩ - b j
def RealPlaceNumericalSetting (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  1 ≤ k ∧ Even k ∧ Formalism.QuantumDeterminants.inWb k r z ∧ 0 < Formalism.QuantumDeterminants.Tz k r z ∧ (∀ a, c a ≠ 0) ∧
    Formalism.QuantumDeterminants.IsHCParam u ∧ Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) ∧ InterlacingCondition k r u v b ∧
    HalfIntegralDifference k r u v b ∧ GapBig k r b
section Defs
variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsHaarOn {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (Formalism.QuantumDeterminants.lmulM s) = μ
def IsQuotMeas (μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  ∀ f : Formalism.QuantumDeterminants.Mt k r → ENNReal, Measurable f →
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν
def IsSPsiEquiv {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ)
    (ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (W : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) : Prop :=
  ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
    W (h * m * g) = ψ m • π h (W g)
def l2SG {Wp : Type*} [NormedAddCommGroup Wp] (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (W : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) : ENNReal :=
  ∫⁻ x, (‖W (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂ν
def rconv {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (e : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (W : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp :=
  fun x => ∫ g, e (Matrix.of g) • W (x * Matrix.of g) ∂μG
def fdegH (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H) : ℝ :=
  ‖w‖ ^ 4 / ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG
def eFun (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  (fdegH μG σ w : ℂ) * star ⟪w, σ g w⟫_ℂ
def ellA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) : ℂ :=
  if h : a.val + 1 < r then g (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩)
  else (g *ᵥ z) (Formalism.QuantumDeterminants.eI k r a)
def psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  Complex.exp (Complex.I * ((∑ a, c a * ellA k r z g a).re : ℂ))
end Defs
def BesselPeriodGGP : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ),
    2 ≤ k → Even k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.IsHCParam u → Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) → InterlacingCondition k r u v b →
    HalfIntegralDifference k r u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μW μN : Measure (Formalism.QuantumDeterminants.Mt k r), IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
  ∃ x x₀ : Mat k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹ ∂(μW.prod μN) ≠ 0
end PI.BesselPeriodGGP


