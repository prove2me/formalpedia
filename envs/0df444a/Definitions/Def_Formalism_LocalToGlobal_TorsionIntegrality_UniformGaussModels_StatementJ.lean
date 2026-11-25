-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_StatementJ
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_StatementJ
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T07:07:17.968893+00:00
-- url     : https://prove2.me/theorems/f63c1d9c-22d5-416c-b441-340519e3e691
-- title:
--   Statement J
-- statement:
--   Definitions and structural lemmas for Statement J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/UniformGaussModels/StatementJ.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_UniformGaussModelConditionEquivalent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_ThetaInZIsThetaLog
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_OneLetterGaussEvery
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
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
open Formalism.DworkPowerSeriesWeights.OddLevelGainBounds (WcapOneLetter JnumOneLetter kaMaxOneLetter)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog alG capG lsG deLoss dSet oddT lamF InClass hhS uS sSub)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom Th alphaQ kernel4
  LocalStandard KappaExists)
def ThmAEntryEveryH : Prop :=
  LocalStandard → KappaExists →
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l,
    Formalism.L2.Th1.CM.IsGoodModel l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (lam : ℂ) (hlam : lam ≠ 0), ‖s2‖ ≤ 1 ∧ IsLTNorm l (cmL a₀ b₀ dK ha hdK lam hlam) ι g2 g3 s2 ε ∧
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∃ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ∧
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]), IsFrameH σ ι g₁ γ B' →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (d N0 N1 : ℕ) [NeZero d], 2 ≤ d → Even d →
  ∀ (ιr : Type) [Fintype ιr] [DecidableEq ιr] (om oms : ιr → MaximalUnramifiedExtension l), OwOK d σ om oms →
    TrDual d σ om oms → (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ d - 1)) →
  ∀ (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    ∀ δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l],
      (∀ P ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ P‖ ≤ 1) →
      ‖δ (frameJet colN p hp I (thetaInZ l (MaximalUnramifiedExtension l).subtype σ om oms (inHyp l f f' (thetaH l ι B' h t θ))))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))
def ThmAGaussEveryH : Prop :=
  LocalStandard → KappaExists →
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l,
    Formalism.L2.Th1.CM.IsGoodModel l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (lam : ℂ) (hlam : lam ≠ 0), ‖s2‖ ≤ 1 ∧ IsLTNorm l (cmL a₀ b₀ dK ha hdK lam hlam) ι g2 g3 s2 ε ∧
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∃ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ∧
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]), IsFrameH σ ι g₁ γ B' →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (d N0 N1 : ℕ) [NeZero d], 2 ≤ d → Even d →
  ∀ (ιr : Type) [Fintype ιr] [DecidableEq ιr] (om oms : ιr → MaximalUnramifiedExtension l), OwOK d σ om oms →
    TrDual d σ om oms → (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ d - 1)) →
  ∀ (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    ∀ n : (ZMod d × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff n (frameJet colN p hp I
          (thetaInZ l (MaximalUnramifiedExtension l).subtype σ om oms (inHyp l f f' (thetaH l ι B' h t θ))))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))
def OneLetterGaussEveryH : Prop :=
  LocalStandard → KappaExists →
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l,
    Formalism.L2.Th1.CM.IsGoodModel l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (lam : ℂ) (hlam : lam ≠ 0), ‖s2‖ ≤ 1 ∧ IsLTNorm l (cmL a₀ b₀ dK ha hdK lam hlam) ι g2 g3 s2 ε ∧
  ∀ (N0 N1 : ℕ) (h : Matrix (Fin N0 × Fin N1) (Fin N0 × Fin N1) ℂ)
    (Λ : AddSubgroup (Fin N0 × Fin N1 → ℂ)) (g₀ : (Fin 4 × Fin N0 × Fin N1 → ℂ) ≃ₗ[ℂ] (Fin 4 × Fin N0 × Fin N1 → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × Fin N0 × Fin N1))) g₀ →
  ∃ g₁ : (Fin 4 × Fin N0 × Fin N1 → ℂ) ≃ₗ[ℂ] (Fin 4 × Fin N0 × Fin N1 → ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × Fin N0 × Fin N1)) (g₁ : (Fin 4 × Fin N0 × Fin N1 → ℂ) →ₗ[ℂ] (Fin 4 × Fin N0 × Fin N1 → ℂ)) ∧
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × Fin N0 × Fin N1)) (imgLat (g₁ : (Fin 4 × Fin N0 × Fin N1 → ℂ) →ₗ[ℂ] (Fin 4 × Fin N0 × Fin N1 → ℂ)) (pow4 Λ)) ∧
  ∀ (t : Fin N0 × Fin N1 → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ (γ : Matrix (Fin 4 × Fin N0 × Fin N1) (Fin 4 × Fin N0 × Fin N1) (MaximalUnramifiedExtension l)) (B' : Matrix (Fin N0 × Fin N1) (Fin N0 × Fin N1) ℂ_[l]), IsFrameH σ ι g₁ γ B' →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (C : ℕ),
  ∀ (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) (a : ℕ), 1 ≤ a →
    (∑ c, p c) ≤ a → ∀ n : (Fin N0 × Fin N0) →₀ ℕ,
    ‖MvPolynomial.coeff n (frameJetOne p hp I
        (MvPowerSeries.subst (fun x => at1 x (expF ℂ_[l] l)) (thetaH l ι B' h t θ)))‖ ≤
      ‖(l : ℂ_[l])‖ ^ (rho l * ((∑ c, p c : ℕ) : ℝ) -
        ((N0 : ℝ) * N1) * (Real.logb l (a : ℝ) + 1))
def CMThetaKernelEveryInertPrime : Prop :=
  LocalStandard → KappaExists →
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l,
    Formalism.L2.Th1.CM.IsGoodModel l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (lam : ℂ) (hlam : lam ≠ 0), ‖s2‖ ≤ 1 ∧ IsLTNorm l (cmL a₀ b₀ dK ha hdK lam hlam) ι g2 g3 s2 ε ∧
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∃ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ∧
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]), IsFrameH σ ι g₁ γ B' →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (ν r0 r1 : ℕ) [NeZero ν] (om oms : Fin ν → MaximalUnramifiedExtension l), OwOK (2 * ν) σ om oms →
    TrDual (2 * ν) σ om oms →
  ∀ (f f' : Fin ν × Fin r0 × Fin r1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
    ∀ (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1) n,
      ‖MvPolynomial.coeff n (frameJet colN hts hp I (thetaInZ (d := 2 * ν) l (MaximalUnramifiedExtension l).subtype σ om oms (inHyp l f f' (thetaH l ι B' h t θ))))‖ ≤
          (l : ℝ) ^ (-(excessGain (l : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss l r0 r1 TT (alG TT colN hts) (lsG TT colN hts)))) ∧
      ‖MvPolynomial.coeff n (frameJet colN hts hp I (thetaInZ (d := 2 * ν) l (MaximalUnramifiedExtension l).subtype σ om oms (inHyp l f f' (thetaH l ι B' h t θ))))‖ ≤
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
            (frameJet colN hts hp I (thetaInZ (d := 2 * ν) l (MaximalUnramifiedExtension l).subtype σ om oms (inHyp l f f' (thetaH l ι B' h t θ))))‖ ≤
          (l : ℝ) ^ (-(gainG (l : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss l r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))
def ThmSEveryH : Prop :=
  LocalStandard → KappaExists →
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l,
    Formalism.L2.Th1.CM.IsGoodModel l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (lam : ℂ) (hlam : lam ≠ 0), ‖s2‖ ≤ 1 ∧ IsLTNorm l (cmL a₀ b₀ dK ha hdK lam hlam) ι g2 g3 s2 ε ∧
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∃ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ∧
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]), IsFrameH σ ι g₁ γ B' →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (ν r0 r1 : ℕ) [NeZero ν],
    ∃ cS : MaximalUnramifiedExtension l, ‖cS‖ ≤ 1 ∧ σ (σ cS) = cS ∧
    ∀ (om oms : Fin ν → MaximalUnramifiedExtension l) (ϖ : ℂ_[l]) (μ : PowerSeries ℂ_[l]),
      ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l]) → OwOK (2 * ν) σ om oms → TrDual (2 * ν) σ om oms →
      PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF l ϖ) : PowerSeries ℂ_[l]) = PowerSeries.X →
    ∀ (f f' : Fin ν × Fin r0 × Fin r1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
      InClass (l : ℂ_[l]) (hhS l (uS ((cS : MaximalUnramifiedExtension l) : ℂ_[l]) ((σ cS : MaximalUnramifiedExtension l) : ℂ_[l])))
        (MvPowerSeries.subst
          (fun x => MvPowerSeries.C ϖ * sSub (conjJ (MaximalUnramifiedExtension l).subtype σ om) (conjJ (MaximalUnramifiedExtension l).subtype σ oms) μ x)
          (inHyp l f f' (thetaH l ι B' h t θ)))
def MatrixEntriesSharpTranslate : Prop :=
  LocalStandard → KappaExists →
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l,
    Formalism.L2.Th1.CM.IsGoodModel l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (lam : ℂ) (hlam : lam ≠ 0), ‖s2‖ ≤ 1 ∧ IsLTNorm l (cmL a₀ b₀ dK ha hdK lam hlam) ι g2 g3 s2 ε ∧
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∃ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ∧
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]), IsFrameH σ ι g₁ γ B' →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (d N0 N1 : ℕ) [NeZero d], 2 ≤ d → Even d → 0 < N0 →
  ∀ (ιr : Type) [Fintype ιr] [DecidableEq ιr] (om oms : ιr → MaximalUnramifiedExtension l), OwOK d σ om oms →
    TrDual d σ om oms → (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ d - 1)) →
  ∀ (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    (∀ s, JnumOneLetter l d TT nu1 size s + (if s ∈ TT then 1 else 0) ≤ N0) →
    ∀ δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l],
      (∀ P ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ P‖ ≤ 1) →
      ‖δ (frameJet colN p hp I (thetaInZ l (MaximalUnramifiedExtension l).subtype σ om oms (inHyp l f f' (thetaH l ι B' h t θ))))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (kaMaxOneLetter d TT nu1 nu2 : ℝ) + 1))
def GaussFormSharpTranslate : Prop :=
  LocalStandard → KappaExists →
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l,
    Formalism.L2.Th1.CM.IsGoodModel l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (lam : ℂ) (hlam : lam ≠ 0), ‖s2‖ ≤ 1 ∧ IsLTNorm l (cmL a₀ b₀ dK ha hdK lam hlam) ι g2 g3 s2 ε ∧
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∃ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ∧
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]), IsFrameH σ ι g₁ γ B' →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (d N0 N1 : ℕ) [NeZero d], 2 ≤ d → Even d → 0 < N0 →
  ∀ (ιr : Type) [Fintype ιr] [DecidableEq ιr] (om oms : ιr → MaximalUnramifiedExtension l), OwOK d σ om oms →
    TrDual d σ om oms → (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ d - 1)) →
  ∀ (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    (∀ s, JnumOneLetter l d TT nu1 size s + (if s ∈ TT then 1 else 0) ≤ N0) →
    ∀ n : (ZMod d × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff n (frameJet colN p hp I
          (thetaInZ l (MaximalUnramifiedExtension l).subtype σ om oms (inHyp l f f' (thetaH l ι B' h t θ))))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (kaMaxOneLetter d TT nu1 nu2 : ℝ) + 1))
def OneLetterGaussSharpTranslate : Prop :=
  LocalStandard → KappaExists →
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l,
    Formalism.L2.Th1.CM.IsGoodModel l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (lam : ℂ) (hlam : lam ≠ 0), ‖s2‖ ≤ 1 ∧ IsLTNorm l (cmL a₀ b₀ dK ha hdK lam hlam) ι g2 g3 s2 ε ∧
  ∀ (N0 N1 : ℕ) (h : Matrix (Fin N0 × Fin N1) (Fin N0 × Fin N1) ℂ)
    (Λ : AddSubgroup (Fin N0 × Fin N1 → ℂ)) (g₀ : (Fin 4 × Fin N0 × Fin N1 → ℂ) ≃ₗ[ℂ] (Fin 4 × Fin N0 × Fin N1 → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × Fin N0 × Fin N1))) g₀ →
  ∃ g₁ : (Fin 4 × Fin N0 × Fin N1 → ℂ) ≃ₗ[ℂ] (Fin 4 × Fin N0 × Fin N1 → ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × Fin N0 × Fin N1)) (g₁ : (Fin 4 × Fin N0 × Fin N1 → ℂ) →ₗ[ℂ] (Fin 4 × Fin N0 × Fin N1 → ℂ)) ∧
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × Fin N0 × Fin N1)) (imgLat (g₁ : (Fin 4 × Fin N0 × Fin N1 → ℂ) →ₗ[ℂ] (Fin 4 × Fin N0 × Fin N1 → ℂ)) (pow4 Λ)) ∧
  ∀ (t : Fin N0 × Fin N1 → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ (γ : Matrix (Fin 4 × Fin N0 × Fin N1) (Fin 4 × Fin N0 × Fin N1) (MaximalUnramifiedExtension l)) (B' : Matrix (Fin N0 × Fin N1) (Fin N0 × Fin N1) ℂ_[l]), IsFrameH σ ι g₁ γ B' →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (C : ℕ),
  ∀ (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1),
    ∀ n : (Fin N0 × Fin N0) →₀ ℕ,
    ‖MvPolynomial.coeff n (frameJetOne p hp I
        (MvPowerSeries.subst (fun x => at1 x (expF ℂ_[l] l)) (thetaH l ι B' h t θ)))‖ ≤
      ‖(l : ℂ_[l])‖ ^ (rho l * ((∑ c, p c : ℕ) : ℝ) -
        ((N0 : ℝ) * N1) * (Real.logb l (C : ℝ) + 1))
end Formalism.L2.Th1.Top


