-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_UniformGaussModelConditionEquivalent
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_UniformGaussModelConditionEquivalent
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:42:55.722514+00:00
-- url     : https://prove2.me/theorems/a385d284-7a30-40dc-b63b-5f57c5d82bd6
-- title:
--   Uniform Gauss Model Condition Equivalent
-- statement:
--   Definitions and structural lemmas for Uniform Gauss Model Condition Equivalent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/UniformGaussModels/UniformGaussModelConditionEquivalent.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_UniformGaussModelCondition
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
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
namespace Formalism.L2.Th1.Top
open Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (lgF UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4
  LocalStandard KappaExists TransInt)
def IsLTNorm (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 s2 ε : MaximalUnramifiedExtension l) : Prop :=
  ι L.g₂ = (ε : ℂ_[l]) ^ 4 * (g2 : ℂ_[l]) ∧ ι L.g₃ = (ε : ℂ_[l]) ^ 6 * (g3 : ℂ_[l]) ∧
    ι (Formalism.L2.Th1.F.s2 L) = (ε : ℂ_[l]) ^ 2 * (s2 : ℂ_[l])
def IsLatH (L : PeriodPair) (b : ℤ) (d : ℕ) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : Prop :=
  IsIsom (matH (blk4 h)) (stdH L (Fin 4 × n)) (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
  IsSelfDual (matH h) Λ ∧ (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b d • x ∈ Λ) ∧
  relIdx (stdLat L (Fin 4 × n)) (imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 ∧
  relIdx (imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) (stdLat L (Fin 4 × n)) ≠ 0
def IsFrameH {l : ℕ} [Fact l.Prime] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (ι : ℂ ≃+* ℂ_[l]) {n : Type} [Fintype n]
    [DecidableEq n] (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]) : Prop :=
  IsUnitaryK σ γ ∧ ∀ (i' : Fin 4) (i : n) (w : Fin 4 × n),
    ∑ j, B' i j * ((γ (i', j) w : MaximalUnramifiedExtension l) : ℂ_[l]) = ι (g.symm (Pi.single w 1) (i', i))
def thetaH (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) {n : Type} [Fintype n] [DecidableEq n]
    (B' : Matrix n n ℂ_[l]) (h : Matrix n n ℂ) (t : n → ℂ) (θ : (n → ℂ) → ℂ) : MvPowerSeries n ℂ_[l] :=
  Formalism.L2.Th1.H.thetaU (ι : ℂ →+* ℂ_[l]) (lgF ℂ_[l] l) B' (Formalism.L2.Th1.H.opU (matH h) t θ)
def TransIntLT : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]),
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, IsLTNorm l L ι g2 g3 s2 ε → ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 →
    ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    TransInt l L ι ω₀ (lgF ℂ_[l] l) (phL l g2 g3 s2 ε)
def uniformGaussModelConditionReformulated₂ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]),
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, IsLTNorm l L ι g2 g3 s2 ε → ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 →
    ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (α : (n → ℂ) → ℂ) (β : (Fin 4 × n → ℂ) → ℂ) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)),
    Formalism.L2.Th1.H.StdData L ω₀ h Λ α β g →
    ¬ l ∣ relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
  ∀ e : ℂ, ‖ι e‖ ≤ 1 → ∀ θ ∈ Th (matH h) α Λ, Formalism.L2.Th1.H.tens4 θ = e • kernel4 L ω₀ Λ β g →
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]),
    IsFrameH σ ι g γ B' → uniformGaussModelCondition l g2 g3 s2 ε (thetaH l ι B' h t θ) γ
def uniformGaussModelConditionEquivalent : Prop :=
  LocalStandard → KappaExists →
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ ι : ℂ ≃+* ℂ_[l],
  ∃ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ∧
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, IsLTNorm l (cmL a₀ b₀ dK ha hdK lam hlam) ι g2 g3 s2 ε → ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 →
    ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]),
    IsFrameH σ ι g₁ γ B' → uniformGaussModelCondition l g2 g3 s2 ε (thetaH l ι B' h t θ) γ
def LTNormExists : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 s2 ε : MaximalUnramifiedExtension l) (c : ℂ) (hc : c ≠ 0),
    ‖ε‖ = 1 → (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ →
    (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ →
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) →
    ∃ (lam : ℂ) (hlam : lam ≠ 0), IsLTNorm l (Formalism.L2.Th1.F.scalePair L lam hlam) ι g2 g3 s2 ε
end Formalism.L2.Th1.Top


