-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:14.691897+00:00
-- url     : https://prove2.me/theorems/97a96d05-f6ea-4c9e-81ac-6a714e5723e4
-- title:
--   Mul Defs
-- statement:
--   Definitions and structural lemmas for Mul Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/MulDefs.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_StAddRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.GalTorsConj.W
open Formalism.L2.Th1.F
def TorsField : Prop :=
  ∀ (L : PeriodPair) (M : IntermediateField ℚ ℂ), L.g₂ ∈ M → L.g₃ ∈ M →
    ∃ M₁ : IntermediateField ℚ ℂ, M ≤ M₁ ∧ (∀ x ∈ M₁, IsAlgebraic M x) ∧
      ∀ (n : ℕ) (t : ℂ), 0 < n → (n : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
        L.weierstrassP t ∈ M₁ ∧ L.derivWeierstrassP t ∈ M₁
def ExtRho : Prop :=
  ∀ (M M₁ : IntermediateField ℚ ℂ) (h : M ≤ M₁), (∀ x ∈ M₁, IsAlgebraic M x) →
    ∀ ρ : M →ₐ[ℚ] ℂ, ∃ ρ₁ : M₁ →ₐ[ℚ] ℂ, ∀ x : M, ρ₁ (IntermediateField.inclusion h x) = ρ x
def Descent : Prop :=
  ∀ (M M₁ : IntermediateField ℚ ℂ) (h : M ≤ M₁), (∀ x ∈ M₁, IsAlgebraic M x) →
    ∀ x : M₁, (∀ σ : M₁ →ₐ[ℚ] ℂ, (∀ y : M, σ (IntermediateField.inclusion h y) = (y : ℂ)) →
      σ x = (x : ℂ)) → (x : ℂ) ∈ M
def veluF (L : PeriodPair) (S : Finset ℂ) (z : ℂ) : ℂ :=
  L.weierstrassP z + ∑ P ∈ S, (L.weierstrassP (z + P) - L.weierstrassP P)
def veluD (L : PeriodPair) (S : Finset ℂ) (z : ℂ) : ℂ :=
  L.derivWeierstrassP z + ∑ P ∈ S, L.derivWeierstrassP (z + P)
def veluU (L : PeriodPair) (S : Finset ℂ) : Set ℂ :=
  {z | z ∉ L.lattice ∧ ∀ P ∈ S, z + P ∉ L.lattice}
def IsogD : Prop :=
  ∀ (L : PeriodPair) (c : ℂ) (S : Finset ℂ), c ≠ 0 → MulStable L c → IsKerReps L c S →
    ∀ z, c * z ∉ L.lattice → c ^ 3 * L.derivWeierstrassP (c * z) = veluD L S z
def TorsDense : Prop :=
  ∀ L : PeriodPair, Dense {t : ℂ | ∃ n : ℕ, 0 < n ∧ (n : ℂ) * t ∈ L.lattice}
def IsogODE : Prop :=
  ∀ (L : PeriodPair) (c : ℂ) (S : Finset ℂ), c ≠ 0 → (∀ P ∈ S, P ∉ L.lattice) →
    (∀ P ∈ S, ∀ Q ∈ S, P - Q ∈ L.lattice → P = Q) →
    (∀ z ∈ veluU L S, veluD L S z ^ 2 =
      4 * veluF L S z ^ 3 - c ^ 4 * L.g₂ * veluF L S z - c ^ 6 * L.g₃) →
    MulStable L c ∧ (∀ P ∈ S, c * P ∈ L.lattice) ∧
      ∀ z ∈ veluU L S, c * z ∉ L.lattice ∧ c ^ 2 * L.weierstrassP (c * z) = veluF L S z ∧
        c ^ 3 * L.derivWeierstrassP (c * z) = veluD L S z
def MulSt : Prop :=
  ∀ (L L' : PeriodPair) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hg2 : L.g₂ ∈ M)
    (hg3 : L.g₃ ∈ M), L'.g₂ = ρ ⟨_, hg2⟩ → L'.g₃ = ρ ⟨_, hg3⟩ →
    ∀ c : ℂ, MulStable L c → ∀ hc : c ∈ M, ρ ⟨c, hc⟩ = c →
      ∀ t t', St L L' M ρ t t' → St L L' M ρ (c * t) (c * t')
end PI.GalTorsConj.W
end


