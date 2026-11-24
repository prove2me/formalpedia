-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RelativeThetaFactorization
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RelativeThetaFactorization
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:33.669869+00:00
-- url     : https://prove2.me/theorems/707e2c14-7370-4b50-a92d-0c0bf8828ce8
-- title:
--   Relative Theta Factorization
-- statement:
--   Definitions and structural lemmas for Relative Theta Factorization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/RelativeThetaFactorization.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementB
import Definitions.Def_Formalism_GaussJetBounds_StatementW
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog bSum idM serAlong)
open Formalism.InvariantFactorPaths.G7 (Simeq UnrOK IsLawOfLog)
def RelativeThetaFactorization : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d] (σ : K0 →+* K0) (j : K0 →+* K),
    UnrOK K0 l σ → (∀ a, ‖j a‖ = ‖a‖) → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K0, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K0), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K0, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ (τ : Type) [Fintype τ] (U0 Φ : MvPowerSeries ((Bool × ι × Fin N0 × Fin N1) ⊕ τ) K)
      (Ψ : MvPowerSeries τ K), Integral U0 → MvPowerSeries.constantCoeff Φ = 0 →
      Simeq Φ (serAlong Sum.inl (sumE (MvPowerSeries.map j be0)) + serAlong Sum.inr Ψ) →
      ∃ U : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1 ⊕ τ) K, Integral U ∧
        ∀ g : Formalism.DworkPowerSeriesWeights.ZV d N0 N1 → MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K,
          (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
          (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
          MvPowerSeries.subst
              (Sum.elim (fun x => serAlong Sum.inl (xOfZ (d := d) l j σ om oms x))
                (fun y => (MvPowerSeries.X (Sum.inr y) :
                  MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1 ⊕ τ) K)))
              (mvExp (-Φ) * U0) =
            MvPowerSeries.subst
                (Sum.elim (fun x => serAlong Sum.inl (g x))
                  (fun y => (MvPowerSeries.X (Sum.inr y) :
                    MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1 ⊕ τ) K))) U *
              serAlong Sum.inl (mvExp (-(bSum (idM : Formalism.DworkPowerSeriesWeights.ZV d N0 N1 → Formalism.DworkPowerSeriesWeights.ZV d N0 N1 → K)
                (MvPowerSeries.map j (beMean l σ be0 om oms ζ))))) *
              serAlong Sum.inr (mvExp (-Ψ))
end Formalism.L2.Th1.D


