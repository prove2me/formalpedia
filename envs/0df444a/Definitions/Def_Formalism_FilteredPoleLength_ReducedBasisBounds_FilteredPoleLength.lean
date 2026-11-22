-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_FilteredPoleLength
-- name    : Formalism_FilteredPoleLength_ReducedBasisBounds_FilteredPoleLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:42:00.233797+00:00
-- url     : https://prove2.me/theorems/6b3f936f-268f-47e9-9264-4aa6fcd59ecf
-- title:
--   Filtered Pole Length
-- statement:
--   Definitions and structural lemmas for Filtered Pole Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/ReducedBasisBounds/FilteredPoleLength.lean

import Mathlib
import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeBaseChangeAlt
open Module Matrix
def SumFromPage : Prop :=
  ∀ (d PP D κ T c RR ga C k f b m δ₂ q DF g₀ : ℝ), 0 ≤ d → 0 < T → T ≤ ga → 0 < PP → 0 ≤ D →
    1 ≤ RR → 0 < q → 0 ≤ C → 0 ≤ k → 0 ≤ f → 0 ≤ b → 0 < m → 0 < δ₂ →
    κ ≤ C * k * f * b →
    3 * C * PP ^ 2 * D ^ 3 * k / (m * δ₂) ≤ T →
    c = RR * PP * DF ^ 2 / q → 1 ≤ g₀ → T * c * g₀ ≤ 1 → PP ^ 2 ≤ f * m * b * δ₂ / 3 →
    RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q → 1 + PP ^ 2 / T ≤ PP ^ 2 * D ^ 3 →
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) ≤ d * f * m * b * δ₂
def RRcBound : Prop :=
  ∀ (RR PP DF q c : ℝ), 1 ≤ RR → 0 < PP → 0 < q → RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q →
    c = RR * PP * DF ^ 2 / q → RR ^ 2 * c ≤ 1 / PP ^ 2
def OrdPoleJoint : Prop :=
  ∀ (ep T : ℕ) (e o : ℤ) (ν vf ve : ℝ), 1 ≤ ep → 0 ≤ vf → 0 ≤ ve → ve < 1 / (ep : ℝ) →
    (o : ℝ) = (ep : ℝ) * ((e : ℝ) + vf - (T : ℝ) * ν - ve) →
      -(max 0 ⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉) ≤ o
def PoleLengthPoint : Prop :=
  ∀ (O' OS K V : Type) [CommRing O'] [IsLocalRing O'] [CommRing OS] [IsDomain OS]
    [IsDiscreteValuationRing OS] [Algebra O' OS] [IsLocalHom (algebraMap O' OS)] [Field K]
    [Algebra OS K] [IsFractionRing OS K] [AddCommGroup V] [Module K V] [Module OS V]
    [IsScalarTower OS K V] [Module O' V] [IsScalarTower O' OS V] [FiniteDimensional K V]
    (ϖ : OS), Irreducible ϖ → ∀ (A : Submodule OS V) (mm : ℕ), Formalism.LatticeIndexTer.IsLat OS K V A →
      let B : Submodule OS V :=
        A.map ((((algebraMap OS K ϖ) ^ (-(mm : ℤ))) • LinearMap.id : V →ₗ[K] V).restrictScalars OS)
      Module.length O' (↥B ⧸ A.comap B.subtype) =
        ((mm * finrank K V : ℕ) : ℕ∞) * Module.length (IsLocalRing.ResidueField O')
          (IsLocalRing.ResidueField OS)
def NormalisedValSum : Prop :=
  ∀ (ι Λ : Type) [Fintype ι] [Fintype Λ] [DecidableEq ι] (p : Λ → ι) (f : Λ → ℝ) (ordv : Λ → ℝ)
    (logN : ι → ℝ) (logNl : Λ → ℝ) (d nK n₁ : ℝ), 0 < d → 0 < nK → nK * d = n₁ →
    (∀ l, logNl l = f l * logN (p l)) →
      (1 / nK) * ∑ i, ((1 / d) * ∑ l ∈ Finset.univ.filter (fun l => p l = i), f l * ordv l) *
          logN i =
        (1 / n₁) * ∑ l, ordv l * logNl l
def DetTermBound : Prop :=
  ∀ (S M δ L ρ PP κ : ℝ), 0 ≤ ρ → 0 ≤ PP → 1 ≤ κ → S = M + δ →
    M ≤ ρ * ((1 / 2) * Real.log ρ + L) → L ≤ PP * κ + PP ^ 2 + PP * κ →
    δ ≤ ρ * PP * (κ + 1) → Real.log ρ ≤ PP * κ →
      S ≤ ρ * (PP ^ 2 + 9 / 2 * PP) * κ
def ComplexHadamard : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (A : ℝ), (∀ i j, ‖M i j‖ ≤ A) →
    ‖M.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2) ∧
      ‖M.det‖ ≤ (Real.sqrt n * A) ^ n
def LossSum : Prop :=
  ∀ (ι : Type) [Fintype ι] (be l vdd vcc vg₁ vg₂ : ι → ℝ) (κ e lrd lcc lg₁ lg₂ : ℝ),
    (∀ i, 0 ≤ l i) →
    (∀ i, be i ≤ κ * (vdd i + vcc i + (e + 1) * vg₁ i + vg₂ i)) →
    ∑ i, vdd i * l i = lrd → ∑ i, vcc i * l i = lcc → ∑ i, vg₁ i * l i = lg₁ →
    ∑ i, vg₂ i * l i = lg₂ →
      ∑ i, be i * l i ≤ κ * (lrd + lcc + (e + 1) * lg₁ + lg₂)
def SchurHalf : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (y₁₁ : K) (y₁₂ : Matrix (Fin 1) (Fin n) K)
    (y₂₁ : Matrix (Fin n) (Fin 1) K) (Y₂₂ : Matrix (Fin n) (Fin n) K), IsUnit Y₂₂.det →
    let s : K := (y₁₂ * Y₂₂⁻¹ * y₂₁) 0 0
    let α : K := y₁₁ - s
    α ≠ 0 →
    let Y : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) K := fromBlocks (of fun _ _ => y₁₁) y₁₂ y₂₁ Y₂₂
    let Y' : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) K :=
      fromBlocks (of fun _ _ => α + s / 2) ((1 / 2 : K) • y₁₂) ((1 / 2 : K) • y₂₁) ((1 / 2 : K) • Y₂₂)
    Y⁻¹ (Sum.inl 0) (Sum.inl 0) = α⁻¹ ∧ Y'⁻¹ (Sum.inl 0) (Sum.inl 0) = α⁻¹
def ShearedBoxVolume : Prop :=
  ∀ (f : ℕ) (M R : ℝ) (s : Fin f → ℝ), 0 < M → 0 < R →
    MeasureTheory.volume
        {p : (Fin f → ℝ) × (Fin f → ℝ) | ∀ τ, |p.1 τ| ≤ M ∧ |p.1 τ * s τ - p.2 τ| ≤ R / M} =
      ENNReal.ofReal (4 ^ f * R ^ f)
def ShearMinkowski : Prop :=
  ∀ (f : ℕ) (N R₀ R covol : ℝ), 1 ≤ f → 0 < N → 0 < R₀ → covol ≤ N * R₀ ^ f →
    R = R₀ * N ^ (1 / (f : ℝ)) → 2 ^ (2 * f) * covol ≤ 4 ^ f * R ^ f
def FilteredPoleLength : Prop :=
  ∀ (O' Rr A : Type) [CommRing O'] [IsLocalRing O'] [CommRing Rr] [IsLocalRing Rr] [Algebra O' Rr]
    [IsLocalHom (algebraMap O' Rr)] [AddCommGroup A] [Module Rr A] [Module O' A]
    [IsScalarTower O' Rr A] (x : Rr) (mm n : ℕ) (F : ℕ → Submodule Rr A) (r : ℕ → ℕ),
    F 0 = ⊤ → F n = ⊥ → (∀ k, k < n → F (k + 1) ≤ F k) →
    (∀ k, k < n → ∀ a ∈ F k, x • a ∈ F (k + 1) → a ∈ F (k + 1)) →
    (∀ k, k < n →
      Module.length Rr
          (↥(F k) ⧸ (F (k + 1) ⊔ (F k).map ((x ^ mm) • (LinearMap.id : A →ₗ[Rr] A))).comap
            (F k).subtype) = ((r k * mm : ℕ) : ℕ∞)) →
      Module.length O' (A ⧸ (⊤ : Submodule Rr A).map ((x ^ mm) • (LinearMap.id : A →ₗ[Rr] A))) =
        (((∑ k ∈ Finset.range n, r k) * mm : ℕ) : ℕ∞) *
          Module.length (IsLocalRing.ResidueField O') (IsLocalRing.ResidueField Rr)
end Formalism.LatticeBaseChangeAlt


