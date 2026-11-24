-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_ThetaInZIsThetaLog
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_ThetaInZIsThetaLog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:42.466799+00:00
-- url     : https://prove2.me/theorems/1c081403-cffa-4da8-a507-edde0ae8f89d
-- title:
--   Theta In ZIs Theta Log
-- statement:
--   Definitions and structural lemmas for Theta In ZIs Theta Log, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/ThetaInZIsThetaLog.lean

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
open Finset
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog OmOK lamF thetaLog EV alG capG lsG deLoss dSet oddT
  InClass hhS uS sSub)
def ThetaInZIsThetaLog : Prop :=
  ∀ (K0 K : Type) [Field K0] [Field K] (l ν r0 r1 : ℕ) [NeZero ν] (σ : K0 →+* K0) (j : K0 →+* K)
    (om oms : Fin ν → K0) (ϖ : K) (μ : PowerSeries K), 2 ≤ l → ϖ ≠ 0 →
    PowerSeries.constantCoeff μ = 0 →
    (PowerSeries.subst μ (lamF l ϖ) : PowerSeries K) = PowerSeries.X →
    ∀ Tht : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) K,
      thetaInZ (d := 2 * ν) l j σ om oms Tht = thetaLog (conjJ j σ om) (conjJ j σ oms) ϖ μ Tht
def ThmSOfF : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [CompleteSpace K0]
    [NormedField K] [IsUltrametricDist K] [CharZero K] (j : K0 →+* K) (p ν r0 r1 : ℕ) [NeZero ν]
    (σ : K0 →+* K0), (∀ a, ‖j a‖ = ‖a‖) → UnrOK K0 p σ →
    (∃ ζ : K0, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K0, F1 F be → F2 p σ be →
    ∃ c : K0, ‖c‖ ≤ 1 ∧ σ (σ c) = c ∧
    ∀ (om oms : Fin ν → K0) (ϖ : K) (μ : PowerSeries K)
      (U0 Φ : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) K),
      ϖ ^ (p ^ 2 - 1) = (p : K) → OwOK (2 * ν) σ om oms → TrDual (2 * ν) σ om oms →
      PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X → Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 → Simeq Φ (sumE (MvPowerSeries.map j be)) →
      InClass (p : K) (hhS p (uS (j c) (j (σ c))))
        (MvPowerSeries.subst
          (fun x => MvPowerSeries.C ϖ * sSub (conjJ j σ om) (conjJ j σ oms) μ x)
          (mvExp (-Φ) * U0))
def KernelOfF : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0]
    [CompleteSpace K0] (σ : K0 →+* K0), UnrOK K0 p σ → (∃ ζ : K0, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K0, F1 F be → F2 p σ be →
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (j : K0 →+* K) (ν r0 r1 : ℕ)
      [NeZero ν], (∀ a, ‖j a‖ = ‖a‖) → (∃ ϖ : K, ϖ ^ (p ^ 2 - 1) = (p : K)) →
    ∀ (om oms : Fin ν → K0), OwOK (2 * ν) σ om oms → TrDual (2 * ν) σ om oms →
    ∀ (U0 Φ : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) K), Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 → Simeq Φ (sumE (MvPowerSeries.map j be)) →
    ∀ (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1) n,
      ‖MvPolynomial.coeff n (frameJet colN hts hp I (thetaInZ (d := 2 * ν) p j σ om oms (mvExp (-Φ) * U0)))‖ ≤
          (p : ℝ) ^ (-(excessGain (p : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)))) ∧
      ‖MvPolynomial.coeff n (frameJet colN hts hp I (thetaInZ (d := 2 * ν) p j σ om oms (mvExp (-Φ) * U0)))‖ ≤
          (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) -
            ∑ s ∈ TT \ oddT TT, (alG TT colN hts s : ℝ))) ∧
      ∀ i : ℕ, 1 ≤ i →
        ‖(p : K) ^ (∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
            (if s.val % 2 = 0 then
              min (hts s c) i -
                ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card
            else ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card)) *
          MvPolynomial.coeff n
            (frameJet colN hts hp I (thetaInZ (d := 2 * ν) p j σ om oms (mvExp (-Φ) * U0)))‖ ≤
          (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))
end Formalism.L2.Th1.D


