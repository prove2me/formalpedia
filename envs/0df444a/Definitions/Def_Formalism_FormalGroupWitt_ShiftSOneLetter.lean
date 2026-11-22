-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_ShiftSOneLetter
-- name    : Formalism_FormalGroupWitt_ShiftSOneLetter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:40.434739+00:00
-- url     : https://prove2.me/theorems/bbe16f76-e338-4e7e-9048-8e16e6316bf2
-- title:
--   Shift SOne Letter
-- statement:
--   Definitions and structural lemmas for Shift SOne Letter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/ShiftSOneLetter.lean

import Definitions.Def_Formalism_FormalGroupWitt_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
namespace Formalism.FG
open Formalism.G Formalism.LT
def shiftLogS (K : Type u) [Field K] (l : ℕ) (ε : ℤ) (m : ℕ) (j : ZMod m) :
    MvPowerSeries (ZMod m) K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e) then (((ε : K) * l) ^ e)⁻¹ else 0
def ltLogS (K : Type u) [Field K] (l : ℕ) (ε : ℤ) {ι : Type v} [DecidableEq ι] (r : ι) :
    MvPowerSeries ι K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single r ((l ^ 2) ^ e) then (((ε : K) * l) ^ e)⁻¹ else 0
def ShiftSOne : Prop :=
  ∀ (K : Type u) [Field K] (l m : ℕ), shiftLogS K l 1 m = shiftLog K l m
def ShiftSOneLetter : Prop :=
  ∀ (K : Type u) [Field K] (l : ℕ) (ε : ℤ), shiftLogS K l ε 1 0 = ltLogS K l ε (0 : ZMod 1)
def ShiftSFunEq : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (l : ℕ) (hl : l.Prime) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    ∀ (m : ℕ) [NeZero m] (σ : K →+* K),
    IsIdMod2 (shiftLogS K l ε m) ∧
    ∀ j, shiftLogS K l ε m j - (l : K)⁻¹ • ∑ k, ((ε : K) * shiftMat K m j k) •
        MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
          (MvPowerSeries.map σ (shiftLogS K l ε m k)) = MvPowerSeries.X j
def ShiftSGroup : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m],
    ∃ F : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℤ_[l], IsFGL F ∧ IsCommV F ∧
      IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) (shiftLogS ℚ_[l] l ε m)
def ShiftSHeight : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m]
    (F : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℤ_[l]),
    IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) (shiftLogS ℚ_[l] l ε m) →
    ∃ e : ZMod m → MvPowerSeries (ZMod m) ℤ_[l], IsHomV F F e ∧
      (∀ j, MvPowerSeries.subst (fun k => MvPowerSeries.map PadicInt.Coe.ringHom (e k))
          (shiftLogS ℚ_[l] l ε m j) = (l : ℚ_[l]) • shiftLogS ℚ_[l] l ε m j) ∧
      (∀ j n, (l : ℤ_[l]) ∣ MvPowerSeries.coeff n
        (e j - MvPowerSeries.C (ε : ℤ_[l]) * MvPowerSeries.X (j - 1) ^ (l ^ 2))) ∧
      (∀ j n, (l : ℤ_[l]) ∣ MvPowerSeries.coeff n
        (iterV e m j - MvPowerSeries.C ((ε : ℤ_[l]) ^ m) * MvPowerSeries.X j ^ (l ^ (2 * m))))
def ShiftSTeich : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m]
    (F : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℤ_[l]),
    IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) (shiftLogS ℚ_[l] l ε m) →
    ∀ (R : Type u) [CommRing R] [IsDomain R] [CharZero R] (φ : ℤ_[l] →+* R) (w : R),
      w ^ ((l ^ 2) ^ m) = w →
      IsHomV (fun i => MvPowerSeries.map φ (F i)) (fun i => MvPowerSeries.map φ (F i))
        (fun j => MvPowerSeries.C (w ^ ((l ^ 2) ^ j.val)) * MvPowerSeries.X j)
def ShiftSTeichWitt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m]
    (F : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℤ_[l]),
    IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) (shiftLogS ℚ_[l] l ε m) →
    ∃ ζ : WittVector l (AlgebraicClosure (ZMod l)), IsPrimitiveRoot ζ (l ^ (2 * m) - 1) ∧
      IsHomV (fun i => MvPowerSeries.map (zlToW l) (F i))
        (fun i => MvPowerSeries.map (zlToW l) (F i))
        (fun j => MvPowerSeries.C (ζ ^ ((l ^ 2) ^ j.val)) * MvPowerSeries.X j)
def GaussLogShiftS : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m] (c : ℝ), 0 < c →
      c ^ (l ^ 2 - 1) ≤ ‖(l : K)‖ →
      ∀ j, HasGauss c (shiftLogS K l ε m j) ∧ gauss c (shiftLogS K l ε m j) = c
def GaussExpShiftS : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m] (c : ℝ), 0 < c →
      c ^ (l ^ 2 - 1) ≤ ‖(l : K)‖ →
      ∀ g : ZMod m → MvPowerSeries (ZMod m) K, (∀ j, MvPowerSeries.constantCoeff (g j) = 0) →
        (∀ j, MvPowerSeries.subst g (shiftLogS K l ε m j) = MvPowerSeries.X j) →
        ∀ j, HasGauss c (g j) ∧ gauss c (g j) = c
def BridgeLT : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (τ : K →+* K),
    FunctionalEquationSetting K l (l ^ 2) τ → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m]
    (ι : Type v) [Fintype ι] [DecidableEq ι] (M : ZMod m → ι → K),
    (∀ j r, ‖M j r‖ ≤ 1) → (∀ j r, τ (M j r) = M (j + 1) r) →
      ∃ h : ZMod m → MvPowerSeries ι K, (∀ j, MvPowerSeries.constantCoeff (h j) = 0) ∧
        (∀ j, IntegralMv (h j)) ∧
        (∀ j r, MvPowerSeries.coeff (Finsupp.single r 1) (h j) = M j r) ∧
        ∀ j, MvPowerSeries.subst h (shiftLogS K l ε m j) =
          ∑ r, MvPowerSeries.C (M j r) * ltLogS K l ε r
def BridgeLTIso : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (τ : K →+* K),
    FunctionalEquationSetting K l (l ^ 2) τ → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m]
    (ι : Type v) [Fintype ι] [DecidableEq ι] (M : ZMod m → ι → K) (N : ι → ZMod m → K),
    (∀ j r, ‖M j r‖ ≤ 1) → (∀ r j, ‖N r j‖ ≤ 1) → (∀ j r, τ (M j r) = M (j + 1) r) →
    (∀ j k, ∑ r, M j r * N r k = if j = k then 1 else 0) →
    (∀ r s, ∑ j, N r j * M j s = if r = s then 1 else 0) →
    ∀ h : ZMod m → MvPowerSeries ι K, (∀ j, MvPowerSeries.constantCoeff (h j) = 0) →
      (∀ j, MvPowerSeries.subst h (shiftLogS K l ε m j) =
        ∑ r, MvPowerSeries.C (M j r) * ltLogS K l ε r) →
      ∃ h' : ι → MvPowerSeries (ZMod m) K, (∀ r, MvPowerSeries.constantCoeff (h' r) = 0) ∧
        (∀ r, IntegralMv (h' r)) ∧
        (∀ r, MvPowerSeries.subst h' (ltLogS K l ε r) =
          ∑ j, MvPowerSeries.C (N r j) * shiftLogS K l ε m j) ∧
        (∀ j, MvPowerSeries.subst h' (h j) = MvPowerSeries.X j) ∧
        (∀ r, MvPowerSeries.subst h (h' r) = MvPowerSeries.X r)
end Formalism.FG


