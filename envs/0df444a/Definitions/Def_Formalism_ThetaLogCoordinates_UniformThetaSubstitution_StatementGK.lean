-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:53.127802+00:00
-- url     : https://prove2.me/theorems/b5e83937-4037-4051-9388-161498883869
-- title:
--   Statement GK
-- statement:
--   Definitions and structural lemmas for Statement GK, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/StatementGK.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementJ
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
def GenericExistsK : Prop :=
  ∀ (F σ : Type) [NormedField F] [IsUltrametricDist F] [CharZero F] [Finite σ],
    ∃ (K : Type) (_ : NormedField K), IsUltrametricDist K ∧ CharZero K ∧
      ∃ (φ : F →+* K) (Y : σ → K), (∀ z, ‖φ z‖ = ‖z‖) ∧
        ∀ P : MvPolynomial σ F,
          ‖MvPolynomial.eval₂ φ Y P‖ = ⨆ n : σ →₀ ℕ, ‖MvPolynomial.coeff n P‖
def GaussBoundNoOperatorGeneric : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K)
    (F : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → (∀ s, ‖u s‖ ≤ 1) → InClass (p : K) (hhS p u) F →
    ∀ n, ‖MvPolynomial.coeff n (frameJet colN hts hp I F)‖ ≤
      (p : ℝ) ^ (-(excessGain (p : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
          (fun s => (capG TT colN hts s : ℝ))
          (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) +
        rhoP p * ∑ s, ((alG TT colN hts s : ℝ) + lsG TT colN hts s)))
def GaussBoundArbitraryGeneric : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K)
    (F : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → (∀ s, ‖u s‖ ≤ 1) → InClass (p : K) (hhS p u) F →
    ∀ n, ‖MvPolynomial.coeff n (frameJet colN hts hp I F)‖ ≤
      (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
          (fun s => (capG TT colN hts s : ℝ))
          (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) -
        ∑ s ∈ TT \ oddT TT, (alG TT colN hts s : ℝ) +
        rhoP p * ∑ s, ((alG TT colN hts s : ℝ) + lsG TT colN hts s)))
def GaussBK : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (ν r0 r1 i : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K)
    (F : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → 1 ≤ i → (∀ s, ‖u s‖ ≤ 1) → InClass (p : K) (hhS p u) F →
    ∀ n, ‖(p : K) ^ (∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
          (if s.val % 2 = 0 then
            min (hts s c) i - ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card
          else ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card)) *
        MvPolynomial.coeff n (frameJet colN hts hp I F)‖ ≤
      (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
          (fun s => (capG TT colN hts s : ℝ))
          (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) +
        rhoP p * ∑ s, ((alG TT colN hts s : ℝ) + lsG TT colN hts s)))
def KernelValuationBoundUltrametric : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K) (ϖ : K)
    (Th : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) → (∀ s, ‖u s‖ ≤ 1) →
    InClass (p : K) (hhS p u) (MvPowerSeries.subst
      (fun x => MvPowerSeries.C ϖ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) K)) Th) →
    ∀ n, ‖MvPolynomial.coeff n (frameJet colN hts hp I Th)‖ ≤
      (p : ℝ) ^ (-(excessGain (p : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
        (fun s => (capG TT colN hts s : ℝ)) (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))
def KernelBoundArbitrarySizes : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K) (ϖ : K)
    (Th : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) → (∀ s, ‖u s‖ ≤ 1) →
    InClass (p : K) (hhS p u) (MvPowerSeries.subst
      (fun x => MvPowerSeries.C ϖ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) K)) Th) →
    ∀ n, ‖MvPolynomial.coeff n (frameJet colN hts hp I Th)‖ ≤
      (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
        (fun s => (capG TT colN hts s : ℝ)) (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) -
        ∑ s ∈ TT \ oddT TT, (alG TT colN hts s : ℝ)))
def KernelBK : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (ν r0 r1 i : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K) (ϖ : K)
    (Th : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → 1 ≤ i → ϖ ^ (p ^ 2 - 1) = (p : K) → (∀ s, ‖u s‖ ≤ 1) →
    InClass (p : K) (hhS p u) (MvPowerSeries.subst
      (fun x => MvPowerSeries.C ϖ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) K)) Th) →
    ∀ n, ‖(p : K) ^ (∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
          (if s.val % 2 = 0 then
            min (hts s c) i - ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card
          else ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card)) *
        MvPolynomial.coeff n (frameJet colN hts hp I Th)‖ ≤
      (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
        (fun s => (capG TT colN hts s : ℝ)) (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))
def KernelBoundsGeneric : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0]
    [CompleteSpace K0] (σ : K0 →+* K0), UnrOK K0 p σ → (∃ ζ : K0, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K0, BetaHyp p F be →
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (j : K0 →+* K) (ν r0 r1 : ℕ)
      [NeZero ν], (∀ a, ‖j a‖ = ‖a‖) →
    ∀ (om oms : Fin ν → ZMod (2 * ν) → K) (ϖ : K) (μ : PowerSeries K)
      (U0 Φ : MvPowerSeries (Bool × EV ν r0 r1) K),
      ϖ ^ (p ^ 2 - 1) = (p : K) → OmOK p ν om oms →
      PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X → Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 →
      Simeq Φ (∑ e : EV ν r0 r1, MvPowerSeries.subst
        (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
          MvPowerSeries (Bool × EV ν r0 r1) K)) (MvPowerSeries.map j be)) →
    ∀ (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1) n,
      ‖MvPolynomial.coeff n (frameJet colN hts hp I (thetaLog om oms ϖ μ (mvExp (-Φ) * U0)))‖ ≤
          (p : ℝ) ^ (-(excessGain (p : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)))) ∧
      ‖MvPolynomial.coeff n (frameJet colN hts hp I (thetaLog om oms ϖ μ (mvExp (-Φ) * U0)))‖ ≤
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
            (frameJet colN hts hp I (thetaLog om oms ϖ μ (mvExp (-Φ) * U0)))‖ ≤
          (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))
def ChainModel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 2 < p →
    ∃ (K0 : Type) (_ : NormedField K0) (_ : IsUltrametricDist K0) (_ : CharZero K0)
      (_ : CompleteSpace K0) (σ : K0 →+* K0) (F be : MvPowerSeries (Fin 2) K0)
      (K : Type) (_ : NormedField K) (_ : IsUltrametricDist K) (_ : CharZero K) (j : K0 →+* K)
      (ϖ : K) (μ : PowerSeries K),
      UnrOK K0 p σ ∧ (∃ ζ : K0, IsPrimitiveRoot ζ (p ^ 2 - 1)) ∧ IsLawOfLog p F ∧ BetaHyp p F be ∧
        ¬ Simeq be 0 ∧ (∀ a, ‖j a‖ = ‖a‖) ∧ ϖ ^ (p ^ 2 - 1) = (p : K) ∧
        PowerSeries.constantCoeff μ = 0 ∧
        (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X ∧
        OmOK p 1 (fun _ _ => (1 : K)) (fun _ _ => (1 : K))
end Formalism.InvariantFactorPaths.G7


