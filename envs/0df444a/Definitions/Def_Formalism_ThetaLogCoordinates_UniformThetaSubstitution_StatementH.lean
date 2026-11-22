-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementH
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:50.284882+00:00
-- url     : https://prove2.me/theorems/8c40ee75-ded5-422b-80cb-19cce51aaead
-- title:
--   Statement H
-- statement:
--   Definitions and structural lemmas for Statement H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/StatementH.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementG
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
open Formalism.DworkPowerSeriesWeights (Integral frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
def KernelValuationBoundPadic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → ℂ_[p]) (ϖ : ℂ_[p])
    (Th : MvPowerSeries (ZV ν r0 r1) ℂ_[p]) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]) → (∀ s, ‖u s‖ ≤ 1) →
    InClass (p : ℂ_[p]) (hhS p u) (MvPowerSeries.subst
      (fun x => MvPowerSeries.C ϖ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) ℂ_[p])) Th) →
    ∀ n, ‖MvPolynomial.coeff n (frameJet colN hts hp I Th)‖ ≤
      (p : ℝ) ^ (-(excessGain (p : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
        (fun s => (capG TT colN hts s : ℝ)) (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))
def KernelValuationBoundEvenSizes : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → ℂ_[p]) (ϖ : ℂ_[p])
    (Th : MvPowerSeries (ZV ν r0 r1) ℂ_[p]) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]) → (∀ s, ‖u s‖ ≤ 1) →
    InClass (p : ℂ_[p]) (hhS p u) (MvPowerSeries.subst
      (fun x => MvPowerSeries.C ϖ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) ℂ_[p])) Th) →
    ∀ n, ‖MvPolynomial.coeff n (frameJet colN hts hp I Th)‖ ≤
      (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
        (fun s => (capG TT colN hts s : ℝ)) (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) -
        ∑ s ∈ TT \ oddT TT, (alG TT colN hts s : ℝ)))
def KernelB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ν r0 r1 i : ℕ) [NeZero ν] (u : ZMod (2 * ν) → ℂ_[p]) (ϖ : ℂ_[p])
    (Th : MvPowerSeries (ZV ν r0 r1) ℂ_[p]) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → 1 ≤ i → ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]) → (∀ s, ‖u s‖ ≤ 1) →
    InClass (p : ℂ_[p]) (hhS p u) (MvPowerSeries.subst
      (fun x => MvPowerSeries.C ϖ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) ℂ_[p])) Th) →
    ∀ n, ‖(p : ℂ_[p]) ^ (∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
          (if s.val % 2 = 0 then
            min (hts s c) i - ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card
          else ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card)) *
        MvPolynomial.coeff n (frameJet colN hts hp I Th)‖ ≤
      (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
        (fun s => (capG TT colN hts s : ℝ)) (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))
end Formalism.InvariantFactorPaths.G7


