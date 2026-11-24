-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:21:28.509607+00:00
-- url     : https://prove2.me/theorems/209a9783-1772-47b0-b7e1-8677bbbc477e
-- title:
--   Global LUnit
-- statement:
--   Definitions and structural lemmas for Global LUnit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobalLUnit.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitDetRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
abbrev KF (b : ℤ) (d : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({UnitDetRootDefs.cmTheta b d} : Set ℂ)
def IsLUnit (l : ℕ) (x : ℂ) : Prop :=
  x ≠ 0 ∧ ∃ k : ℕ, ¬ l ∣ k ∧ IsIntegral ℤ ((k : ℂ) * x) ∧ IsIntegral ℤ ((k : ℂ) * x⁻¹)
def Hyp (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)) : Prop :=
  UnitDetRootDefs.CmOK a b c d ∧ UnitDetRootDefs.IsSelfDual (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) Λa ∧
    (∀ x ∈ Λa, UnitDetRootDefs.cmTheta b d • x ∈ Λa) ∧
    UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) Λa ≠ 0 ∧
    UnitDetRootDefs.relIdx Λa (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ 0
def admitted (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ))
    (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) : Prop :=
  UnitDetRootDefs.IsIsom (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m)
      (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧
    UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 ∧
    UnitDetRootDefs.relIdx (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ 0
def EqAway {V : Type*} [AddCommGroup V] [Module ℂ V] (l : ℕ) (Λ Λ' : AddSubgroup V) : Prop :=
  ∃ k : ℕ, ¬ l ∣ k ∧ (∀ x ∈ Λ, (k : ℂ) • x ∈ Λ') ∧ (∀ x ∈ Λ', (k : ℂ) • x ∈ Λ)
def DetInK : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
    Hyp a b c d ha hd lam hlam m Λa → ∀ δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ), admitted a b d ha hd lam hlam m Λa δ →
      LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∈ KF b d ∧
      LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) * conj (LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))) = 1
def LocalStd : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
    Hyp a b c d ha hd lam hlam m Λa → ∀ (l : ℕ) [Fact l.Prime] (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)),
      admitted a b d ha hd lam hlam m Λa δ →
      ¬ l ∣ UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) →
      EqAway l (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa)
def GlobalLUnit : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
    Hyp a b c d ha hd lam hlam m Λa → ∃ γ : ℂ, γ ∈ KF b d ∧ γ ≠ 0 ∧ ∃ n : ℕ, 0 < n ∧
      ∀ (l : ℕ) [Fact l.Prime] (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)), admitted a b d ha hd lam hlam m Λa δ →
        EqAway l (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) →
        IsLUnit l (γ / LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ^ n)
def NormOne : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (x : ℂ), IsLUnit l x → ‖ι x‖ = 1
def RootStep : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ), UnitDetRootDefs.CmOK a b c d → ∀ β ∈ KF b d, β * conj β = 1 → ∀ N : ℕ, 0 < N →
    ∃ κ : ℂ, κ ^ N = β⁻¹ ∧ IsAlgebraic ℚ κ ∧ ∀ σ : ℂ ≃+* ℂ, ‖σ κ‖ = 1
def ConjMem : Prop := ∀ (b : ℤ) (d : ℕ) (x : ℂ), x ∈ KF b d → conj x ∈ KF b d
def ConjLUnit : Prop := ∀ (l : ℕ) (x : ℂ), IsLUnit l x → IsLUnit l (conj x)
end PI.UnitaryGroupMassFormula.UnitDetRoot


