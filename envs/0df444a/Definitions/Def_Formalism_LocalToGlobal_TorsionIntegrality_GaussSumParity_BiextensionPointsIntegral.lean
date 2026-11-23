-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:49.196288+00:00
-- url     : https://prove2.me/theorems/ab3dd417-5565-4ff3-873c-64dcb504a49b
-- title:
--   Biextension Points Integral
-- statement:
--   Definitions and structural lemmas for Biextension Points Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/BiextensionPointsIntegral.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementB
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
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
def TilInvariantL : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ u : K, u ^ (l ^ d - 1) = 1 →
    ∀ (τ : Type) [Finite τ] (L : ZMod d → MvPowerSeries τ K), ShiftType l σ L →
      Simeq (MvPowerSeries.subst L (MvPowerSeries.subst (torus l u) (beTil (d := d) l σ be0 om oms)))
        (MvPowerSeries.subst L (beTil (d := d) l σ be0 om oms))
def MeanSimeqL : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ (τ : Type) [Finite τ] (L : ZMod d → MvPowerSeries τ K), ShiftType l σ L →
      Simeq (MvPowerSeries.subst L (beMean (d := d) l σ be0 om oms ζ))
        (MvPowerSeries.subst L (beTil (d := d) l σ be0 om oms))
def BiextensionPointsIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
      ∃ Xt : Bool × ι × Fin N0 × Fin N1 → MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K,
        (∀ x, MvPowerSeries.constantCoeff (Xt x) = 0 ∧ Integral (Xt x)) ∧
        (∀ x, PowerSeries.subst (Xt x) (lgF K l) =
          if x.1 = false then
            linEL σ (oms x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))
          else linOL σ (om x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))) ∧
        Simeq (∑ ab : Fin N0 × Fin N1, MvPowerSeries.subst
            (fun s => entLog (K := K) l (s, ab.1, ab.2)) (beMean (d := d) l σ be0 om oms ζ))
          (MvPowerSeries.subst Xt (sumE be0))
end Formalism.L2.Th1.D


