-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:21.307948+00:00
-- url     : https://prove2.me/theorems/56b852f3-1ae9-4e2f-8ba3-3a5611fe6f14
-- title:
--   Formula Step
-- statement:
--   Definitions and structural lemmas for Formula Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/FormulaStep.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_SMinus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WeylForKWork
open PI PI.UpqRep Matrix
def Blocks : Prop := ∀ (N : ℕ) (ε : Fin N → Bool),
  (∀ h ∈ Kset (allPos (nPl ε)), iPl ε h ∈ Kset ε) ∧
  (∀ h ∈ Kset (allPos (nMi ε)), iMi ε h ∈ Kset ε) ∧
  (∀ h h', iPl ε h * iMi ε h' = iMi ε h' * iPl ε h) ∧
  (∀ g ∈ Kset ε, ∃ h ∈ Kset (allPos (nPl ε)), ∃ h' ∈ Kset (allPos (nMi ε)), g = iPl ε h * iMi ε h') ∧
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)),
    IsURepOn (Kset ε) σ → IsURepOn (Kset (allPos (nPl ε))) (sPl ε σ) ∧ IsURepOn (Kset (allPos (nMi ε))) (sMi ε σ)
def BlockDiag : Prop := ∀ (N : ℕ) (ε : Fin N → Bool),
  (∀ f : Fin N → ℝ, ∑ a, f a = ∑ i, f (ePl ε i) + ∑ j, f (eMi ε j)) ∧
  (∀ θ : Fin (nPl ε) → ℝ, ∃ θ' : Fin N → ℝ, (∀ i, θ' (ePl ε i) = θ i) ∧ (∀ j, θ' (eMi ε j) = 0) ∧
    iPl ε (diagonal fun i => Complex.exp ((θ i : ℂ) * Complex.I)) =
      diagonal fun a => Complex.exp ((θ' a : ℂ) * Complex.I)) ∧
  (∀ θ : Fin (nMi ε) → ℝ, ∃ θ' : Fin N → ℝ, (∀ i, θ' (ePl ε i) = 0) ∧ (∀ j, θ' (eMi ε j) = θ j) ∧
    iMi ε (diagonal fun j => Complex.exp ((θ j : ℂ) * Complex.I)) =
      diagonal fun a => Complex.exp ((θ' a : ℂ) * Complex.I))
def TorusWt : Prop := ∀ (N : ℕ) (ε : Fin N → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (W : Submodule ℂ H),
  IsURepOn (Kset ε) σ → FiniteDimensional ℂ W → W ≠ ⊥ →
  (∀ θ : Fin N → ℝ, ∀ v ∈ W, σ (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) v ∈ W) →
  ∃ μ : Fin N → ℝ, ∃ w ∈ W, w ≠ 0 ∧ IsWtOn (Kset ε) σ μ w
def WtUniq : Prop := ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (μ μ' : Fin n → ℝ) (w : H),
  w ≠ 0 → IsWtOn (Kset (allPos n)) σ μ w → IsWtOn (Kset (allPos n)) σ μ' w → μ = μ'
def MinIrr : Prop := ∀ (p : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (σ₁ : Matrix (Fin p) (Fin p) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (μ : Fin p → ℝ) (v : H),
  IsURepOn (Kset (allPos p)) σ₁ → FiniteDimensional ℂ S → IsKStableOn (allPos p) σ₁ S →
  v ∈ S → v ≠ 0 → IsWtOn (Kset (allPos p)) σ₁ μ v →
  ∃ X : Submodule ℂ H, X ≤ S ∧ IsKStableOn (allPos p) σ₁ X ∧
    (∀ X' : Submodule ℂ H, X' ≤ X → IsKStableOn (allPos p) σ₁ X' → X' = ⊥ ∨ X' = X) ∧
    ∃ x ∈ X, x ≠ 0 ∧ IsWtOn (Kset (allPos p)) σ₁ μ x
def CDomRes : Prop := ∀ (N : ℕ) (ε : Fin N → Bool) (μ Λ : Fin N → ℝ), CDom ε μ Λ →
  CDom (allPos (nPl ε)) (fun i => μ (ePl ε i)) (fun i => Λ (ePl ε i)) ∧
  CDom (allPos (nMi ε)) (fun j => μ (eMi ε j)) (fun j => Λ (eMi ε j))
def DimStep : Prop := ∀ (p q : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (σ₁ : Matrix (Fin p) (Fin p) ℂ → (H →L[ℂ] H)) (σ₂ : Matrix (Fin q) (Fin q) ℂ → (H →L[ℂ] H))
  (S X Y : Submodule ℂ H),
  IsURepOn (Kset (allPos p)) σ₁ → IsURepOn (Kset (allPos q)) σ₂ →
  (∀ h ∈ Kset (allPos p), ∀ h' ∈ Kset (allPos q), (σ₁ h).comp (σ₂ h') = (σ₂ h').comp (σ₁ h)) →
  FiniteDimensional ℂ S → IsKStableOn (allPos p) σ₁ S → IsKStableOn (allPos q) σ₂ S →
  (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn (allPos p) σ₁ S' → IsKStableOn (allPos q) σ₂ S' →
    S' = ⊥ ∨ S' = S) →
  X ≤ S → X ≠ ⊥ → IsKStableOn (allPos p) σ₁ X →
  (∀ X' : Submodule ℂ H, X' ≤ X → IsKStableOn (allPos p) σ₁ X' → X' = ⊥ ∨ X' = X) →
  Y ≤ S → Y ≠ ⊥ → IsKStableOn (allPos q) σ₂ Y →
  (∀ Y' : Submodule ℂ H, Y' ≤ Y → IsKStableOn (allPos q) σ₂ Y' → Y' = ⊥ ∨ Y' = Y) →
  Module.finrank ℂ S = Module.finrank ℂ X * Module.finrank ℂ Y
def FormulaStep : Prop := ∀ (N : ℕ) (ε : Fin N → Bool) (Λ : Fin N → ℝ),
  (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
      ((Λ + rhoC ε) a - (Λ + rhoC ε) b)) /
    ((∏ i ∈ Finset.range (nPl ε), (i.factorial : ℝ)) * ∏ i ∈ Finset.range (nMi ε), (i.factorial : ℝ)) =
  wu (nPl ε) (fun i => Λ (ePl ε i)) * wu (nMi ε) (fun j => Λ (eMi ε j))
def TypePl : Prop := ∀ (N : ℕ) (ε : Fin N → Bool) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
  IsURepOn (Kset ε) σ → IsKTypeOf ε σ Λ S →
  ∃ X : Submodule ℂ H, X ≤ S ∧ IsKTypeOf (allPos (nPl ε)) (sPl ε σ) (fun i => Λ (ePl ε i)) X
def TypeMi : Prop := ∀ (N : ℕ) (ε : Fin N → Bool) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
  IsURepOn (Kset ε) σ → IsKTypeOf ε σ Λ S →
  ∃ Y : Submodule ℂ H, Y ≤ S ∧ IsKTypeOf (allPos (nMi ε)) (sMi ε σ) (fun j => Λ (eMi ε j)) Y
end PI.WeylForKWork


