-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:39:32.164973+00:00
-- url     : https://prove2.me/theorems/82769a3c-d4e4-4150-bba8-ba73710ebe54
-- title:
--   Odd Log Relation
-- statement:
--   Definitions and structural lemmas for Odd Log Relation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/OddLogRelation.lean

import Mathlib
import Definitions.Def_Formalism_GaussJetBounds_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
def lgF (K : Type) [Field K] (p : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n => ∑ j ∈ range (n + 1), if n = (p ^ 2) ^ j then ((p : K) ^ j)⁻¹ else 0
def g0F (K : Type) [Field K] (p : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n =>
    ∑ j ∈ range (n + 1), if n = p * (p ^ 2) ^ j then ((p : K) ^ (j + 1))⁻¹ else 0
def Aser (K : Type) [Field K] (p : ℕ) : MvPowerSeries (Fin 2) K :=
  fun n => ∑ i ∈ range (n 0 + 1), ∑ j ∈ range (n 1 + 1),
    if i ≤ j ∧ n 0 = (p ^ 2) ^ i ∧ n 1 = p * (p ^ 2) ^ j then ((p : K) ^ (i + j + 1))⁻¹ else 0
def Aser' (K : Type) [Field K] (p : ℕ) : MvPowerSeries (Fin 2) K :=
  fun n => ∑ i ∈ range (n 1 + 1), ∑ j ∈ range (n 0 + 1),
    if i ≤ j ∧ n 1 = (p ^ 2) ^ i ∧ n 0 = p * (p ^ 2) ^ j then ((p : K) ^ (i + j + 1))⁻¹ else 0
def Gser {K : Type} [Field K] (p : ℕ) (c c' : K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.C c * Aser K p - MvPowerSeries.C c' * Aser' K p
def at1 {K ι : Type} [Field K] (x : ι) (f : PowerSeries K) : MvPowerSeries ι K :=
  PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K) f
def frobVar {K ι : Type} [Field K] (p : ℕ) (f : MvPowerSeries ι K) : MvPowerSeries ι K :=
  MvPowerSeries.subst (fun i => (MvPowerSeries.X i : MvPowerSeries ι K) ^ p) f
def OddLogRelation : Prop :=
  ∀ (K : Type) [Field K] (p : ℕ), 2 ≤ p → (p : K) ≠ 0 →
    g0F K p = PowerSeries.C ((p : K)⁻¹) *
        (PowerSeries.subst (PowerSeries.X ^ p : PowerSeries K) (lgF K p) : PowerSeries K) ∧
      (PowerSeries.subst (PowerSeries.X ^ p : PowerSeries K) (g0F K p) : PowerSeries K) =
        lgF K p - PowerSeries.X
def IdentityB : Prop :=
  ∀ (K : Type) [Field K] (p : ℕ), 2 ≤ p → (p : K) ≠ 0 →
    frobVar p (Aser K p) =
        MvPowerSeries.C (p : K) * (at1 0 (g0F K p) * at1 1 (lgF K p) - Aser' K p) ∧
      frobVar p (Aser' K p) =
        MvPowerSeries.C (p : K) * (at1 0 (lgF K p) * at1 1 (g0F K p) - Aser K p)
def FrobExprG : Prop :=
  ∀ (K : Type) [Field K] (p : ℕ) (c c' : K), 2 ≤ p → (p : K) ≠ 0 →
    frobVar p (Gser p c' c) - MvPowerSeries.C (p : K) * Gser p c c' =
      MvPowerSeries.C (p : K) *
        (MvPowerSeries.C c' * (at1 0 (g0F K p) * at1 1 (lgF K p)) -
          MvPowerSeries.C c * (at1 0 (lgF K p) * at1 1 (g0F K p)))
def ValTable : Prop :=
  ∀ (p i j : ℕ), 2 ≤ p → i ≤ j →
    (j = 0 → (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ j) / ((p : ℝ) ^ 2 - 1) - (i + j + 1) =
      1 / ((p : ℝ) - 1) - 1) ∧
    (1 ≤ j → 1 / ((p : ℝ) - 1) + p - 2 ≤
      (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ j) / ((p : ℝ) ^ 2 - 1) - (i + j + 1))
def PiFactorial : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (p : ℕ) (ϖ : K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) →
    ∀ i : ℕ, ‖ϖ ^ ((p + 1) * i) / (i.factorial : K)‖ ≤ 1
def ExpIntegral : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ →
    ∀ f : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      (∀ n, ‖MvPowerSeries.coeff n f‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) → Integral (mvExp f)
def InClass {K ι : Type} [NormedField K] (pp : K) (hh F : MvPowerSeries ι K) : Prop :=
  ∃ U : ℕ → MvPowerSeries ι K, (∀ i, Integral (U i)) ∧
    ∀ n : ι →₀ ℕ, MvPowerSeries.coeff n F =
      ∑ i ∈ range (n.degree + 1), (pp ^ i)⁻¹ * MvPowerSeries.coeff n (hh ^ i * U i)
def ClassChange : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] (pp : K), pp ≠ 0 → ‖pp‖ ≤ 1 →
    ∀ hh Y F : MvPowerSeries ι K, MvPowerSeries.constantCoeff hh = 0 →
      MvPowerSeries.constantCoeff Y = 0 → Integral Y →
      InClass pp hh F → InClass pp (hh + MvPowerSeries.C pp * Y) F
def ClassMul : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] (pp : K)
    (hh F V : MvPowerSeries ι K), MvPowerSeries.constantCoeff hh = 0 → Integral V →
    InClass pp hh F → InClass pp hh (F * V)
def ClassSubst : Prop :=
  ∀ (K ι κ : Type) [Finite ι] [NormedField K] [IsUltrametricDist K] (pp : K)
    (hh F : MvPowerSeries ι K) (φ : ι → MvPowerSeries κ K),
    MvPowerSeries.constantCoeff hh = 0 →
    (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → (∀ i, Integral (φ i)) →
    InClass pp hh F → InClass pp (MvPowerSeries.subst φ hh) (MvPowerSeries.subst φ F)
def ClassExp : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) (ϖ : K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) →
    ∀ hh : MvPowerSeries ι K, MvPowerSeries.constantCoeff hh = 0 →
      InClass (p : K) hh (mvExp (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh)))
def Gtot {K E : Type} [Field K] [Fintype E] (p : ℕ) (c c' ϖ : K) : MvPowerSeries (Bool × E) K :=
  ∑ e : E, MvPowerSeries.subst
    (fun a : Fin 2 => MvPowerSeries.C ϖ *
      (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) : MvPowerSeries (Bool × E) K))
    (Gser p c c')
def hh1 {K E : Type} [Field K] [Fintype E] (p : ℕ) (c c' : K) : MvPowerSeries (Bool × E) K :=
  ∑ e : E, (MvPowerSeries.C c * MvPowerSeries.X (false, e) * MvPowerSeries.X (true, e) ^ p -
    MvPowerSeries.C c' * MvPowerSeries.X (false, e) ^ p * MvPowerSeries.X (true, e))
def RescaleExact : Prop :=
  ∀ (K E : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [Fintype E] (p : ℕ)
    (c c' ϖ : K), p.Prime → ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) →
    ‖c‖ ≤ 1 → ‖c'‖ ≤ 1 →
    ∃ V : MvPowerSeries (Bool × E) K, Integral V ∧
      mvExp (-(Gtot (E := E) p c c' ϖ)) =
        mvExp (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh1 (E := E) p c c')) * V
def RescaleCore : Prop :=
  ∀ (K E : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [Fintype E] (p : ℕ)
    (c c' ϖ : K), p.Prime → ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) →
    ‖c‖ ≤ 1 → ‖c'‖ ≤ 1 →
    InClass (p : K) (hh1 (E := E) p c c') (mvExp (-(Gtot (E := E) p c c' ϖ)))
end Formalism.InvariantFactorPaths.G7


