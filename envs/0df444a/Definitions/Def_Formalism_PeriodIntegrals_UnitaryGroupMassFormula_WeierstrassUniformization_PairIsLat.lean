-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeierstrassUniformization_PairIsLat
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeierstrassUniformization_PairIsLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:07.930971+00:00
-- url     : https://prove2.me/theorems/b6c58223-205a-4c8c-820f-53b94aeb8ae9
-- title:
--   Pair Is Lat
-- statement:
--   Definitions and structural lemmas for Pair Is Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeierstrassUniformization/PairIsLat.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeierUnif
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperHalfPlane ModularForm
namespace PI.WU
open PI.WeierUnif
def Bridge : Prop :=
  ∀ L : PeriodPair, g2 L.lattice.toAddSubgroup = L.g₂ ∧ g3 L.lattice.toAddSubgroup = L.g₃
def ToPair : Prop :=
  ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∃ L : PeriodPair, L.lattice.toAddSubgroup = Λ
def PairIsLat : Prop :=
  ∀ L : PeriodPair, IsLat L.lattice.toAddSubgroup
def EisVal : Prop :=
  ∀ (L : PeriodPair) (τ : ℍ) (c : ℂ), c ≠ 0 → L.ω₁ = c * (τ : ℂ) → L.ω₂ = c →
    L.g₂ = (c ^ 4)⁻¹ * (4 * (Real.pi : ℂ) ^ 4 / 3) * E₄ τ ∧
    L.g₃ = (c ^ 6)⁻¹ * (8 * (Real.pi : ℂ) ^ 6 / 27) * E₆ τ
def JSurj : Prop :=
  ∀ C : ℂ, ∃ τ : ℍ, E₄ τ ^ 3 = C * ModularForm.discriminant τ
def Scale : Prop :=
  ∀ a b G2 G3 : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → G2 ^ 3 - 27 * G3 ^ 2 ≠ 0 →
    a ^ 3 * G3 ^ 2 = G2 ^ 3 * b ^ 2 → ∃ c : ℂ, c ≠ 0 ∧ (c ^ 4)⁻¹ * G2 = a ∧ (c ^ 6)⁻¹ * G3 = b
def PEq : Prop :=
  ∀ L L' : PeriodPair, L.g₂ = L'.g₂ → L.g₃ = L'.g₃ →
    L.weierstrassPExcept 0 =ᶠ[nhds 0] L'.weierstrassPExcept 0
def LatOfP : Prop :=
  ∀ L L' : PeriodPair, L.weierstrassPExcept 0 =ᶠ[nhds 0] L'.weierstrassPExcept 0 →
    L.lattice = L'.lattice
def pairOf (c : ℂ) (hc : c ≠ 0) (τ : ℍ) : PeriodPair where
  ω₁ := c * (τ : ℂ)
  ω₂ := c
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : (c : ℂ) * ((s : ℂ) * (τ : ℂ) + (t : ℂ)) = 0 := by
      rw [Complex.real_smul, Complex.real_smul] at hst
      linear_combination hst
    have h2 : (s : ℂ) * (τ : ℂ) + (t : ℂ) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hc
      · exact h
    have him : s * τ.im = 0 := by
      have := congrArg Complex.im h2
      simpa using this
    have hs : s = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact h
      · exact absurd h (ne_of_gt τ.im_pos)
    subst hs
    refine ⟨rfl, ?_⟩
    have := congrArg Complex.re h2
    simpa using this
end PI.WU
end


