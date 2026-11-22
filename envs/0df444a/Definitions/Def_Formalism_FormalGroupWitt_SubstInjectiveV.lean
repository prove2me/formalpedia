-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
-- name    : Formalism_FormalGroupWitt_SubstInjectiveV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:11:07.109135+00:00
-- url     : https://prove2.me/theorems/88b8f665-0dd5-479d-8308-c17cd4bccce5
-- title:
--   Subst Injective V
-- statement:
--   Definitions and structural lemmas for Subst Injective V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/SubstInjectiveV.lean

import Definitions.Def_Formalism_FormalGroupWitt_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v w
namespace Formalism.FG
open Formalism.G Formalism.LT
def SolveExistsV : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) [Fintype ι] [DecidableEq ι] (τ : Type w) [Finite τ]
    (f : ι → MvPowerSeries ι R) (G : ι → MvPowerSeries τ R), IsIdMod2 f →
    (∀ j, MvPowerSeries.constantCoeff (G j) = 0) →
      ∃ h : ι → MvPowerSeries τ R, (∀ i, MvPowerSeries.constantCoeff (h i) = 0) ∧
        ∀ j, MvPowerSeries.subst h (f j) = G j
def SubstInjectiveV : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) [Fintype ι] [DecidableEq ι] (τ : Type w) [Finite τ]
    (f : ι → MvPowerSeries ι R) (a b : ι → MvPowerSeries τ R), IsIdMod2 f →
    (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → (∀ i, MvPowerSeries.constantCoeff (b i) = 0) →
    (∀ j, MvPowerSeries.subst a (f j) = MvPowerSeries.subst b (f j)) → a = b
def CoeffBoundV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ (ι : Type v) [Fintype ι] (M : ι → ι → K), IntegralMat M →
    ∀ (τ : Type w) (f : ι → MvPowerSeries τ K), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) →
      IsFunEqTypeV p q hq σ M f →
      ∀ j (n : τ →₀ ℕ), ∃ k : ℕ, (∀ i, q ^ k ∣ n i) ∧
        ‖MvPowerSeries.coeff n (f j)‖ * ‖(p : K)‖ ^ k ≤ 1
def IntegralSubstV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) [Finite ι] (τ : Type w)
    (g : MvPowerSeries ι K) (a : ι → MvPowerSeries τ K),
    IntegralMv g → (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → (∀ i, IntegralMv (a i)) →
      IntegralMv (MvPowerSeries.subst a g)
def FunEqSubstV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ (ι : Type v) [Fintype ι] (M : ι → ι → K), IntegralMat M →
    ∀ f : ι → MvPowerSeries ι K, (∀ j, MvPowerSeries.constantCoeff (f j) = 0) →
      IsFunEqTypeV p q hq σ M f →
    ∀ (τ : Type w) (α : ι → MvPowerSeries τ K), (∀ i, MvPowerSeries.constantCoeff (α i) = 0) →
      (∀ i, IntegralMv (α i)) →
      IsFunEqTypeV p q hq σ M (fun j => MvPowerSeries.subst α (f j))
def LowCoeffV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K),
    2 ≤ q → ∀ (ι : Type v) [Fintype ι] (M : ι → ι → K) (τ : Type w)
    (D : ι → MvPowerSeries τ K), IsFunEqTypeV p q hq σ M D → ∀ N : ℕ, 1 ≤ N →
      (∀ j (d : τ →₀ ℕ), d.degree < N → MvPowerSeries.coeff d (D j) = 0) →
      ∀ j (d : τ →₀ ℕ), d.degree = N → ‖MvPowerSeries.coeff d (D j)‖ ≤ 1
def InvIntegralV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) [Fintype ι] [DecidableEq ι]
    (τ : Type w) [Finite τ] (C : (ι → MvPowerSeries τ K) → Prop) (f : ι → MvPowerSeries ι K),
    IsIdMod2 f →
    (∀ a b, C a → C b → C (a - b)) →
    (∀ P : ι → MvPowerSeries τ K, (∀ i, MvPowerSeries.constantCoeff (P i) = 0) →
      (∀ i, IntegralMv (P i)) → C (fun j => MvPowerSeries.subst P (f j))) →
    (∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ j (d : τ →₀ ℕ), d.degree < N → MvPowerSeries.coeff d (D j) = 0) →
      ∀ j (d : τ →₀ ℕ), d.degree = N → ‖MvPowerSeries.coeff d (D j)‖ ≤ 1) →
    ∀ h : ι → MvPowerSeries τ K, (∀ i, MvPowerSeries.constantCoeff (h i) = 0) →
      C (fun j => MvPowerSeries.subst h (f j)) → ∀ i, IntegralMv (h i)
def FrobLiftPadicSq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], FunctionalEquationSetting ℚ_[l] l (l ^ 2) (RingHom.id ℚ_[l])
end Formalism.FG


