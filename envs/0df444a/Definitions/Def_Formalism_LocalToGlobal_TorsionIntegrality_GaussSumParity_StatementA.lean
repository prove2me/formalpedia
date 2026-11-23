-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementA
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:58.427633+00:00
-- url     : https://prove2.me/theorems/4c966020-a335-4d1f-bed9-a95af796c907
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/StatementA.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_TrDual
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp Unram NoLowBidegree letterLog de1 de2)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp)
def ExpSpec : Prop :=
  ∀ (K : Type) [Field K] (l : ℕ), 2 ≤ l →
    PowerSeries.constantCoeff (expF K l) = 0 ∧
    PowerSeries.subst (expF K l) (lgF K l) = (PowerSeries.X : PowerSeries K) ∧
    PowerSeries.subst (lgF K l) (expF K l) = (PowerSeries.X : PowerSeries K) ∧
    ∀ ex : PowerSeries K, PowerSeries.constantCoeff ex = 0 →
      PowerSeries.subst ex (lgF K l) = (PowerSeries.X : PowerSeries K) → ex = expF K l
def MulSpec : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ c : K,
    (∃ e : PowerSeries K, IsMul l c e) ∧
    (∀ e e' : PowerSeries K, IsMul l c e → IsMul l c e' → e = e') ∧
    (‖c‖ ≤ 1 → σ (σ c) = c → ∀ e : PowerSeries K, IsMul l c e → ∀ n, ‖PowerSeries.coeff n e‖ ≤ 1)
def TeichSigma : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) (σ : K →+* K),
    UnrOK K l σ → 1 ≤ d → ∀ ζ : K, ζ ^ (l ^ d - 1) = 1 → σ ζ = ζ ^ l
def BeTilXY : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (l d : ℕ) [NeZero d] (σ : K →+* K), 2 ≤ l → Even d →
    ∀ (be0 : MvPowerSeries (Fin 2) K) (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K),
      (∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) → TrDual d σ om oms →
      MvPowerSeries.subst (zXY l σ om oms) (beTil (d := d) l σ be0 om oms) = beXY be0
def BMinus1 : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms →
      ∃ (T : ZMod d → MvPowerSeries (Bool × ι) K) (Xi : Bool × ι → MvPowerSeries (ZMod d) K),
        (∀ s, MvPowerSeries.constantCoeff (T s) = 0 ∧ Integral (T s)) ∧
        (∀ x, MvPowerSeries.constantCoeff (Xi x) = 0 ∧ Integral (Xi x)) ∧
        (∀ s, MvPowerSeries.subst T (letLog (K := K) l s) = zXY l σ om oms s) ∧
        (∀ s x, MvPowerSeries.coeff (Finsupp.single x 1) (T s) = mXY σ om oms s x) ∧
        (∀ s, MvPowerSeries.subst Xi (T s) = MvPowerSeries.X s) ∧
        (∀ x, MvPowerSeries.subst T (Xi x) = MvPowerSeries.X x) ∧
        (∀ s n, MvPowerSeries.coeff n (T s) ≠ 0 → ∀ x, n x ≠ 0 → (x.1 = false ↔ s.val % 2 = 0))
def MeanTorusInvariant : Prop :=
  ∀ (K : Type) [Field K] (l d : ℕ) [NeZero d] (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K)
    (ι : Type) [Fintype ι] (om oms : ι → K) (ζ : K), ζ ^ (l ^ d - 1) = 1 →
    MvPowerSeries.subst (torus l ζ) (beMean (d := d) l σ be0 om oms ζ) = beMean l σ be0 om oms ζ
def MeanNoLowBidegreeTerms : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (l d : ℕ) [NeZero d] (σ : K →+* K), 2 ≤ l → 2 ≤ d → Even d →
    ∀ (be0 : MvPowerSeries (Fin 2) K), DivAB be0 →
    ∀ (ι : Type) [Fintype ι] (om oms : ι → K) (ζ : K), IsPrimitiveRoot ζ (l ^ d - 1) →
      NoLowBidegree (beMean (d := d) l σ be0 om oms ζ)
def TorusSumCoboundaryCondition : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    ∀ (ι : Type) [Fintype ι] (om oms : ι → K), OwOK d σ om oms →
      Simeq (MvPowerSeries.subst (letterLog (K := K) l) (de1 (beTil (d := d) l σ be0 om oms))) 0 ∧
      Simeq (MvPowerSeries.subst (letterLog (K := K) l) (de2 (beTil (d := d) l σ be0 om oms))) 0
def MeanBiextensionHypothesesOfCocycle : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    ∀ (ι : Type) [Fintype ι] (om oms : ι → K), OwOK d σ om oms →
    ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
      BHyp l d ⊤ ζ (beMean l σ be0 om oms ζ)
def TilInvariant : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ u : K, u ^ (l ^ d - 1) = 1 →
      Simeq (MvPowerSeries.subst (letLog (K := K) l)
          (MvPowerSeries.subst (torus l u) (beTil (d := d) l σ be0 om oms)))
        (MvPowerSeries.subst (letLog (K := K) l) (beTil (d := d) l σ be0 om oms))
def MeanSimeq : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
      Simeq (MvPowerSeries.subst (letLog (K := K) l) (beMean (d := d) l σ be0 om oms ζ))
        (MvPowerSeries.subst (letLog (K := K) l) (beTil (d := d) l σ be0 om oms)) ∧
      Simeq (MvPowerSeries.subst (zXY l σ om oms) (beMean (d := d) l σ be0 om oms ζ)) (beXY be0)
def BetaHypOfF : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ F be0 : MvPowerSeries (Fin 2) K, F1 F be0 → F2 l σ be0 → BetaHyp l F be0
end Formalism.L2.Th1.D


