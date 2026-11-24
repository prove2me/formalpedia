-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:30.557499+00:00
-- url     : https://prove2.me/theorems/67e1fe5f-f9e0-4180-99a2-a6544a584ddc
-- title:
--   Cauchy HW
-- statement:
--   Definitions and structural lemmas for Cauchy HW, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/CauchyHW.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
namespace PI.FJM
def bRow {σ : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) : Module.End ℂ (MvPolynomial σ ℂ) :=
  ∑ k : Fin n, LinearMap.mulLeft ℂ (X (ι (a, k))) * (pderiv (ι (b, k))).toLinearMap
def bCol {σ : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) : Module.End ℂ (MvPolynomial σ ℂ) :=
  ∑ i : Fin m, LinearMap.mulLeft ℂ (X (ι (i, c))) * (pderiv (ι (i, d))).toLinearMap
def CauchyHW : Prop := ∀ (σ : Type) (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι →
  ∀ (α : Fin m → ℕ) (β : Fin n → ℕ) (P : MvPolynomial σ ℂ), P ≠ 0 →
  (∀ a b : Fin m, a < b → bRow ι a b P = 0) → (∀ c d : Fin n, c < d → bCol ι c d P = 0) →
  (∀ e ∈ P.support, (∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) ∧ (∀ k, ∑ i : Fin m, e (ι (i, k)) = β k)) →
  (∀ i, 0 < α i) → (∀ k, 0 < β k) →
  m = n ∧ Antitone α ∧ (∀ (i : Fin m) (k : Fin n), (i : ℕ) = k → α i = β k) ∧
    ∃ Q : MvPolynomial σ ℂ, (∀ e ∈ Q.support, ∀ x, e (ι x) = 0) ∧
      P = shapeProd (Matrix.of fun (i : Fin m) (k : Fin n) => (X (ι (i, k)) : MvPolynomial σ ℂ)) (List.ofFn α) * Q
def MinDegJ : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
  ∀ P ∈ JH p q r s μ μ', P ≠ 0 →
    (∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
    (∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ' ∧ P ∈ homog (Ix p q × Ix r s) d)
abbrev nu1 (p q r s : ℕ) (μ : Ix p q → ℚ) : Ix p q → ℚ := shiftNu (cPair r s) μ
abbrev nu2 (p q r s : ℕ) (μ' : Ix r s → ℚ) : Ix r s → ℚ := shiftNu (cPair p q) μ'
def MinHyp (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s) : Prop :=
  P ∈ JH p q r s μ μ' ∧ P ≠ 0 ∧ ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ (d : ℚ) = degW (cPair p q) μ' ∧
    P ∈ homog (Ix p q × Ix r s) d
def PureJ : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  ∀ e ∈ P.support, ∀ l : Ln p q r s, e l ≠ 0 →
    nu1 p q r s μ l.1 ≠ 0 ∧ nu2 p q r s μ' l.2 ≠ 0 ∧
    (linePos l = true ↔ 0 < nu1 p q r s μ l.1) ∧ (linePos l = true ↔ 0 < nu2 p q r s μ' l.2)
def SegJ : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  (∀ i i' : Fin p, i < i' → 0 < nu1 p q r s μ (.inl i') → 0 < nu1 p q r s μ (.inl i)) ∧
  (∀ i i' : Fin p, i < i' → nu1 p q r s μ (.inl i) < 0 → nu1 p q r s μ (.inl i') < 0) ∧
  (∀ j j' : Fin q, j < j' → 0 < nu1 p q r s μ (.inr j') → 0 < nu1 p q r s μ (.inr j)) ∧
  (∀ j j' : Fin q, j < j' → nu1 p q r s μ (.inr j) < 0 → nu1 p q r s μ (.inr j') < 0) ∧
  (∀ k k' : Fin r, k < k' → 0 < nu2 p q r s μ' (.inl k') → 0 < nu2 p q r s μ' (.inl k)) ∧
  (∀ k k' : Fin r, k < k' → nu2 p q r s μ' (.inl k) < 0 → nu2 p q r s μ' (.inl k') < 0) ∧
  (∀ l l' : Fin s, l < l' → 0 < nu2 p q r s μ' (.inr l') → 0 < nu2 p q r s μ' (.inr l)) ∧
  (∀ l l' : Fin s, l < l' → nu2 p q r s μ' (.inr l) < 0 → nu2 p q r s μ' (.inr l') < 0)
end PI.FJM


