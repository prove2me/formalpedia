-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementP
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:19:09.485508+00:00
-- url     : https://prove2.me/theorems/1fb8ad48-d5d1-43fe-813f-91e4d43e7b98
-- title:
--   Statement P
-- statement:
--   Definitions and structural lemmas for Statement P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/StatementP.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
namespace Formalism.L2.Th1.E
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq cob IsLawOfLog lgF UnrOK)
section Prod
variable {K : Type} [Field K]
def phSum {n : Type} [Fintype n] (ph : PowerSeries K) : MvPowerSeries n K := ∑ i, at1 i ph
def thetaProd {κ n : Type} [Fintype κ] [Fintype n] (r : κ → K) (H : κ → n → PowerSeries K) :
    MvPowerSeries n K :=
  ∑ k, MvPowerSeries.C (r k) * ∏ i, at1 i (H k i)
def hypCoord {O ι n : Type} [Semiring O] [Fintype ι] (l linv : PowerSeries K) (τ : O →+* K) (f f' : ι → n → O) (i : n) :
    MvPowerSeries (Bool × ι) K :=
  Formalism.L2.Th1.C.flin l linv (Sum.elim (fun e => τ (f e i)) (fun e => τ (f' e i)))
    (Sum.elim (fun e => (MvPowerSeries.X (false, e) : MvPowerSeries (Bool × ι) K))
      (fun e => MvPowerSeries.X (true, e)))
def beSum {ι : Type} [Fintype ι] (l linv ph : PowerSeries K) : MvPowerSeries (Bool × ι) K :=
  ∑ e, Formalism.L2.Th1.C.be0 l linv ph (MvPowerSeries.X (false, e)) (MvPowerSeries.X (true, e))
end Prod
def ProdInt : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (κ n : Type) [Fintype κ] [Fintype n]
    (ph : PowerSeries K) (r : κ → K) (V : κ → n → PowerSeries K),
    constantCoeff ph = 0 → (∀ k, ‖r k‖ ≤ 1) → (∀ k i, IntS (V k i)) →
      thetaProd r (fun k i => (mvExp (-ph) : PowerSeries K) * V k i) =
          mvExp (-(phSum ph : MvPowerSeries n K)) * thetaProd r V ∧
        Integral (thetaProd r V)
def SubstExpInt : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (n m : Type) [Fintype n]
    (φ : n → MvPowerSeries m K), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → (∀ i, Integral (φ i)) →
    ∀ Φ U : MvPowerSeries n K, MvPowerSeries.constantCoeff Φ = 0 → Integral U →
      MvPowerSeries.subst φ (mvExp (-Φ) * U) =
          mvExp (-(MvPowerSeries.subst φ Φ)) * MvPowerSeries.subst φ U ∧
        Integral (MvPowerSeries.subst φ U) ∧ MvPowerSeries.constantCoeff (MvPowerSeries.subst φ Φ) = 0
def CongIffSimeq : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (R : Subring K),
    (∀ a, a ∈ R ↔ ‖a‖ ≤ 1) → ∀ (σ : Type) (f g : MvPowerSeries σ K),
      Formalism.L2.Th1.C.Cong R f g ↔ Simeq f g
def IntHyp : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (R : Subring K),
    (∀ a, a ∈ R ↔ ‖a‖ ≤ 1) → ∀ (l linv ph : PowerSeries K), Formalism.L2.Th1.C.Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, Formalism.L2.Th1.C.EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → Formalism.L2.Th1.C.IsBinomScalar R (τ z)) →
    Formalism.L2.Th1.C.F1 R l linv ph →
    (∀ α : O, Formalism.L2.Th1.C.PhNormAt R l linv ph (τ α) (τ (star α))) →
    (∀ α : O, Formalism.L2.Th1.C.AdjAt R l linv ph (τ α) (τ (star α))) →
    ∀ (n ι : Type) [Fintype n] [Fintype ι] [DecidableEq ι] (f f' : ι → n → O),
    (∀ e e', ∑ i, star (f e i) * f e' i = 0) → (∀ e e', ∑ i, star (f' e i) * f' e' i = 0) →
    (∀ e e', ∑ i, star (f e i) * f' e' i = if e = e' then 1 else 0) →
    ∀ (κ : Type) [Fintype κ] (r : κ → K) (V : κ → n → PowerSeries K),
      (∀ k, ‖r k‖ ≤ 1) → (∀ k i, IntS (V k i)) →
      ∃ U0 Φ : MvPowerSeries (Bool × ι) K, Integral U0 ∧ MvPowerSeries.constantCoeff Φ = 0 ∧
        Simeq Φ (beSum l linv ph) ∧
        MvPowerSeries.subst (hypCoord l linv τ f f')
            (thetaProd r (fun k i => (mvExp (-ph) : PowerSeries K) * V k i)) = mvExp (-Φ) * U0
def SumEBridge : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (l linv : PowerSeries K), Formalism.L2.Th1.C.IsLogPair l linv →
    ∀ F : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff F = 0 → cob F l = 0 →
    ∀ (ph : PowerSeries K) (ι : Type) [Fintype ι] (N0 N1 : ℕ),
      (Formalism.L2.Th1.D.sumE (cob F ph) : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K) =
        beSum l linv ph
def MapCob : Prop :=
  ∀ (K0 K : Type) [Field K0] [Field K] (j : K0 →+* K) (F : MvPowerSeries (Fin 2) K0) (f : PowerSeries K0),
    MvPowerSeries.constantCoeff F = 0 →
      MvPowerSeries.map j (cob F f) = cob (MvPowerSeries.map j F) (PowerSeries.map j f)
def IntThetaZ : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d] (σ : K0 →+* K0) (j : K0 →+* K),
    UnrOK K0 l σ → (∀ a, ‖j a‖ = ‖a‖) → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ ph0 : PowerSeries K0, constantCoeff ph0 = 0 →
    Formalism.L2.Th1.D.F1 F (cob F ph0) → Formalism.L2.Th1.D.F2 l σ (cob F ph0) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K0), Formalism.L2.Th1.D.OwOK d σ om oms →
      Formalism.L2.Th1.D.TrDual d σ om oms → ∀ ζ : K0, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ (R : Subring K), (∀ a, a ∈ R ↔ ‖a‖ ≤ 1) →
    Formalism.L2.Th1.C.Frame R (lgF K l) (Formalism.L2.Th1.D.expF K l) (PowerSeries.map j ph0) →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, Formalism.L2.Th1.C.EndInt R (lgF K l) (Formalism.L2.Th1.D.expF K l) (τ α)) →
    (∀ z : O, star z = z → Formalism.L2.Th1.C.IsBinomScalar R (τ z)) →
    Formalism.L2.Th1.C.F1 R (lgF K l) (Formalism.L2.Th1.D.expF K l) (PowerSeries.map j ph0) →
    (∀ α : O, Formalism.L2.Th1.C.PhNormAt R (lgF K l) (Formalism.L2.Th1.D.expF K l) (PowerSeries.map j ph0)
      (τ α) (τ (star α))) →
    (∀ α : O, Formalism.L2.Th1.C.AdjAt R (lgF K l) (Formalism.L2.Th1.D.expF K l) (PowerSeries.map j ph0)
      (τ α) (τ (star α))) →
    ∀ (n : Type) [Fintype n] (f f' : ι × Fin N0 × Fin N1 → n → O),
    (∀ e e', ∑ i, star (f e i) * f e' i = 0) → (∀ e e', ∑ i, star (f' e i) * f' e' i = 0) →
    (∀ e e', ∑ i, star (f e i) * f' e' i = if e = e' then 1 else 0) →
    ∀ (κ : Type) [Fintype κ] (r : κ → K) (V : κ → n → PowerSeries K),
      (∀ k, ‖r k‖ ≤ 1) → (∀ k i, IntS (V k i)) →
      ∃ U : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K, Integral U ∧
        ∀ g : Formalism.DworkPowerSeriesWeights.ZV d N0 N1 → MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K,
          (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
          (∀ y, MvPowerSeries.subst g (Formalism.DworkPowerSeriesWeights.entLog (K := K) l y) = MvPowerSeries.X y) →
          Formalism.L2.Th1.D.thetaInZ l j σ om oms
                    (MvPowerSeries.subst (hypCoord (lgF K l) (Formalism.L2.Th1.D.expF K l) τ f f')
                      (thetaProd r (fun k i => (mvExp (-(PowerSeries.map j ph0)) : PowerSeries K) * V k i))) =
            Formalism.DworkPowerSeriesWeights.thetaZ g U (-1) (MvPowerSeries.map j (Formalism.L2.Th1.D.beMean l σ (cob F ph0) om oms ζ))
end Formalism.L2.Th1.E


