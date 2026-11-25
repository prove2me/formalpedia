-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_StatementB
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_StatementB
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:02.925862+00:00
-- url     : https://prove2.me/theorems/e14bbf4e-bf8b-5cd7-865a-c9f2ab355af7
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/UniformGaussModels/StatementB.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_IsHypPair
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_OneLetterGaussEvery
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
namespace Formalism.L2.Th1.Top
open Formalism.L2.Th1.D
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights (Integral frameJet frameJetOne nablaO)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog alG capG lsG deLoss dSet oddT)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
def ThmAEntryOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l],
  ∃ (g2 g3 ε s2 : MaximalUnramifiedExtension l) (c : ℂ) (hc : c ≠ 0), Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 ∧ ‖ε‖ = 1 ∧
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧ ‖s2‖ ≤ 1 ∧
    (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
    (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) ∧
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (d N0 N1 : ℕ) [NeZero d], 2 ≤ d → Even d →
  ∀ (ιr : Type) [Fintype ιr] [DecidableEq ιr] (om oms : ιr → MaximalUnramifiedExtension l), OwOK d σ om oms →
    TrDual d σ om oms → (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ d - 1)) →
  ∀ (n : Type) [Fintype n] (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ ω₀ : ℂ, ω₀ ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice → ω₀ / 2 ∉ (Formalism.L2.Th1.F.scalePair L c hc).lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[l]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ l ∣ N → (∀ k i, (N : ℂ) * s k i ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    ∀ δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l],
      (∀ P ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ P‖ ≤ 1) →
      ‖δ (frameJet colN p hp I (thetaInZ l (MaximalUnramifiedExtension l).subtype σ om oms (thetaHyp l (Formalism.L2.Th1.F.scalePair L c hc) ι (ε : ℂ_[l]) ω₀ f f' r s)))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))
def ThmAGaussOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l],
  ∃ (g2 g3 ε s2 : MaximalUnramifiedExtension l) (c : ℂ) (hc : c ≠ 0), Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 ∧ ‖ε‖ = 1 ∧
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧ ‖s2‖ ≤ 1 ∧
    (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
    (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) ∧
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (d N0 N1 : ℕ) [NeZero d], 2 ≤ d → Even d →
  ∀ (ιr : Type) [Fintype ιr] [DecidableEq ιr] (om oms : ιr → MaximalUnramifiedExtension l), OwOK d σ om oms →
    TrDual d σ om oms → (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ d - 1)) →
  ∀ (n : Type) [Fintype n] (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ ω₀ : ℂ, ω₀ ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice → ω₀ / 2 ∉ (Formalism.L2.Th1.F.scalePair L c hc).lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[l]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ l ∣ N → (∀ k i, (N : ℂ) * s k i ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    ∀ n : (ZMod d × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff n (frameJet colN p hp I
          (thetaInZ l (MaximalUnramifiedExtension l).subtype σ om oms (thetaHyp l (Formalism.L2.Th1.F.scalePair L c hc) ι (ε : ℂ_[l]) ω₀ f f' r s)))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))
def OneLetterGaussOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l],
  ∃ (g2 g3 ε s2 : MaximalUnramifiedExtension l) (c : ℂ) (hc : c ≠ 0), Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 ∧ ‖ε‖ = 1 ∧
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧ ‖s2‖ ≤ 1 ∧
    (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
    (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) ∧
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (N0 N1 C : ℕ),
  ∀ ω₀ : ℂ, ω₀ ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice → ω₀ / 2 ∉ (Formalism.L2.Th1.F.scalePair L c hc).lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[l]) (s : κ → Fin N0 × Fin N1 → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ l ∣ N → (∀ k i, (N : ℂ) * s k i ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice) →
  ∀ (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) (a : ℕ), 1 ≤ a →
    (∑ c, p c) ≤ a → ∀ n : (Fin N0 × Fin N0) →₀ ℕ,
    ‖MvPolynomial.coeff n (frameJetOne p hp I
        (MvPowerSeries.subst (fun x => at1 x (expF ℂ_[l] l)) (thetaOrth l (Formalism.L2.Th1.F.scalePair L c hc) ι (ε : ℂ_[l]) ω₀ r s)))‖ ≤
      ‖(l : ℂ_[l])‖ ^ (rho l * ((∑ c, p c : ℕ) : ℝ) -
        ((N0 : ℝ) * N1) * (Real.logb l (a : ℝ) + 1))
def KernelOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l],
  ∃ (g2 g3 ε s2 : MaximalUnramifiedExtension l) (c : ℂ) (hc : c ≠ 0), Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 ∧ ‖ε‖ = 1 ∧
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧ ‖s2‖ ≤ 1 ∧
    (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
    (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) ∧
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (ν r0 r1 : ℕ) [NeZero ν] (om oms : Fin ν → MaximalUnramifiedExtension l), OwOK (2 * ν) σ om oms →
    TrDual (2 * ν) σ om oms →
  ∀ (n : Type) [Fintype n] (f f' : Fin ν × Fin r0 × Fin r1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ ω₀ : ℂ, ω₀ ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice → ω₀ / 2 ∉ (Formalism.L2.Th1.F.scalePair L c hc).lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[l]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ l ∣ N → (∀ k i, (N : ℂ) * s k i ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice) →
    ∀ (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1) n,
      ‖MvPolynomial.coeff n (frameJet colN hts hp I (thetaInZ (d := 2 * ν) l (MaximalUnramifiedExtension l).subtype σ om oms (thetaHyp l (Formalism.L2.Th1.F.scalePair L c hc) ι (ε : ℂ_[l]) ω₀ f f' r s)))‖ ≤
          (l : ℝ) ^ (-(excessGain (l : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss l r0 r1 TT (alG TT colN hts) (lsG TT colN hts)))) ∧
      ‖MvPolynomial.coeff n (frameJet colN hts hp I (thetaInZ (d := 2 * ν) l (MaximalUnramifiedExtension l).subtype σ om oms (thetaHyp l (Formalism.L2.Th1.F.scalePair L c hc) ι (ε : ℂ_[l]) ω₀ f f' r s)))‖ ≤
          (l : ℝ) ^ (-(gainG (l : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss l r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) -
            ∑ s ∈ TT \ oddT TT, (alG TT colN hts s : ℝ))) ∧
      ∀ i : ℕ, 1 ≤ i →
        ‖(l : ℂ_[l]) ^ (∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
            (if s.val % 2 = 0 then
              min (hts s c) i -
                ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card
            else ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card)) *
          MvPolynomial.coeff n
            (frameJet colN hts hp I (thetaInZ (d := 2 * ν) l (MaximalUnramifiedExtension l).subtype σ om oms (thetaHyp l (Formalism.L2.Th1.F.scalePair L c hc) ι (ε : ℂ_[l]) ω₀ f f' r s)))‖ ≤
          (l : ℝ) ^ (-(gainG (l : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss l r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))
def ThmAEntryEveryOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (c : ℂ) (hc : c ≠ 0), ‖s2‖ ≤ 1 ∧
    (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
    (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) ∧
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (d N0 N1 : ℕ) [NeZero d], 2 ≤ d → Even d →
  ∀ (ιr : Type) [Fintype ιr] [DecidableEq ιr] (om oms : ιr → MaximalUnramifiedExtension l), OwOK d σ om oms →
    TrDual d σ om oms → (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ d - 1)) →
  ∀ (n : Type) [Fintype n] (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ ω₀ : ℂ, ω₀ ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice → ω₀ / 2 ∉ (Formalism.L2.Th1.F.scalePair L c hc).lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[l]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ l ∣ N → (∀ k i, (N : ℂ) * s k i ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    ∀ δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l],
      (∀ P ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ P‖ ≤ 1) →
      ‖δ (frameJet colN p hp I (thetaInZ l (MaximalUnramifiedExtension l).subtype σ om oms (thetaHyp l (Formalism.L2.Th1.F.scalePair L c hc) ι (ε : ℂ_[l]) ω₀ f f' r s)))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))
def ThmAGaussEveryOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (c : ℂ) (hc : c ≠ 0), ‖s2‖ ≤ 1 ∧
    (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
    (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) ∧
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (d N0 N1 : ℕ) [NeZero d], 2 ≤ d → Even d →
  ∀ (ιr : Type) [Fintype ιr] [DecidableEq ιr] (om oms : ιr → MaximalUnramifiedExtension l), OwOK d σ om oms →
    TrDual d σ om oms → (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ d - 1)) →
  ∀ (n : Type) [Fintype n] (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ ω₀ : ℂ, ω₀ ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice → ω₀ / 2 ∉ (Formalism.L2.Th1.F.scalePair L c hc).lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[l]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ l ∣ N → (∀ k i, (N : ℂ) * s k i ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    ∀ n : (ZMod d × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff n (frameJet colN p hp I
          (thetaInZ l (MaximalUnramifiedExtension l).subtype σ om oms (thetaHyp l (Formalism.L2.Th1.F.scalePair L c hc) ι (ε : ℂ_[l]) ω₀ f f' r s)))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))
def OneLetterGaussEveryOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (c : ℂ) (hc : c ≠ 0), ‖s2‖ ≤ 1 ∧
    (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
    (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) ∧
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (N0 N1 C : ℕ),
  ∀ ω₀ : ℂ, ω₀ ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice → ω₀ / 2 ∉ (Formalism.L2.Th1.F.scalePair L c hc).lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[l]) (s : κ → Fin N0 × Fin N1 → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ l ∣ N → (∀ k i, (N : ℂ) * s k i ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice) →
  ∀ (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) (a : ℕ), 1 ≤ a →
    (∑ c, p c) ≤ a → ∀ n : (Fin N0 × Fin N0) →₀ ℕ,
    ‖MvPolynomial.coeff n (frameJetOne p hp I
        (MvPowerSeries.subst (fun x => at1 x (expF ℂ_[l] l)) (thetaOrth l (Formalism.L2.Th1.F.scalePair L c hc) ι (ε : ℂ_[l]) ω₀ r s)))‖ ≤
      ‖(l : ℂ_[l])‖ ^ (rho l * ((∑ c, p c : ℕ) : ℝ) -
        ((N0 : ℝ) * N1) * (Real.logb l (a : ℝ) + 1))
def KernelEveryOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (c : ℂ) (hc : c ≠ 0), ‖s2‖ ≤ 1 ∧
    (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
    (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) ∧
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (ν r0 r1 : ℕ) [NeZero ν] (om oms : Fin ν → MaximalUnramifiedExtension l), OwOK (2 * ν) σ om oms →
    TrDual (2 * ν) σ om oms →
  ∀ (n : Type) [Fintype n] (f f' : Fin ν × Fin r0 × Fin r1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ ω₀ : ℂ, ω₀ ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice → ω₀ / 2 ∉ (Formalism.L2.Th1.F.scalePair L c hc).lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[l]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ l ∣ N → (∀ k i, (N : ℂ) * s k i ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice) →
    ∀ (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1) n,
      ‖MvPolynomial.coeff n (frameJet colN hts hp I (thetaInZ (d := 2 * ν) l (MaximalUnramifiedExtension l).subtype σ om oms (thetaHyp l (Formalism.L2.Th1.F.scalePair L c hc) ι (ε : ℂ_[l]) ω₀ f f' r s)))‖ ≤
          (l : ℝ) ^ (-(excessGain (l : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss l r0 r1 TT (alG TT colN hts) (lsG TT colN hts)))) ∧
      ‖MvPolynomial.coeff n (frameJet colN hts hp I (thetaInZ (d := 2 * ν) l (MaximalUnramifiedExtension l).subtype σ om oms (thetaHyp l (Formalism.L2.Th1.F.scalePair L c hc) ι (ε : ℂ_[l]) ω₀ f f' r s)))‖ ≤
          (l : ℝ) ^ (-(gainG (l : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss l r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) -
            ∑ s ∈ TT \ oddT TT, (alG TT colN hts s : ℝ))) ∧
      ∀ i : ℕ, 1 ≤ i →
        ‖(l : ℂ_[l]) ^ (∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
            (if s.val % 2 = 0 then
              min (hts s c) i -
                ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card
            else ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card)) *
          MvPolynomial.coeff n
            (frameJet colN hts hp I (thetaInZ (d := 2 * ν) l (MaximalUnramifiedExtension l).subtype σ om oms (thetaHyp l (Formalism.L2.Th1.F.scalePair L c hc) ι (ε : ℂ_[l]) ω₀ f f' r s)))‖ ≤
          (l : ℝ) ^ (-(gainG (l : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss l r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))
end Formalism.L2.Th1.Top


