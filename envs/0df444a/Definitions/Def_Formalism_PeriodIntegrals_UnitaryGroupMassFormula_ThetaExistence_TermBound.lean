-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaExistence_TermBound
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaExistence_TermBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:29.354835+00:00
-- url     : https://prove2.me/theorems/b3c78fca-eefa-41f7-8e63-1266b4193e14
-- title:
--   Term Bound
-- statement:
--   Definitions and structural lemmas for Term Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaExistence/TermBound.lean

import Definitions.Def_Formalism_PeriodIntegrals_ThGExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.ThGW
section Defs
variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]
noncomputable def kerA (A : ℝ) (a : T → I → J → ℂ) : (T → I → J → ℂ) → ℂ :=
  fun z => Complex.exp ((Real.pi : ℂ) * HfG A z a)
noncomputable def poin (s A : ℝ) (La : AddSubgroup (T → I → J → ℂ)) (a : T → I → J → ℂ) :
    (T → I → J → ℂ) → ℂ :=
  fun z => ∑' x : La, alG s A (x : T → I → J → ℂ) * UG A (x : T → I → J → ℂ) (kerA A a) z
end Defs
def GaussSumm : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (ι : Type) [Fintype ι]
    (b : Module.Basis ι ℝ (T → I → J → ℂ)) (c C : ℝ), 0 < c →
    Summable (fun x : AddSubgroup.closure (Set.range b) =>
      Real.exp (-c * ‖(x : T → I → J → ℂ)‖ ^ 2 + C * ‖(x : T → I → J → ℂ)‖))
def TermBound : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ x a z : T → I → J → ℂ,
      ‖alG s A x * UG A x (kerA A a) z‖ ≤
        Real.exp (Real.pi * (Fintype.card T * Fintype.card I * Fintype.card J : ℝ) *
            (‖z‖ * ‖a‖ + ‖x‖ * ‖a‖ + ‖z‖ * ‖x‖) / A - Real.pi * ‖x‖ ^ 2 / (2 * A))
def PoinHol : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La : AddSubgroup (T → I → J → ℂ), GoodLat s A La →
      ∀ a : T → I → J → ℂ, Differentiable ℂ (poin s A La a)
def PoinInv : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La : AddSubgroup (T → I → J → ℂ), GoodLat s A La →
      ∀ a : T → I → J → ℂ, ∀ y ∈ La, ∀ z, alG s A y * UG A y (poin s A La a) z = poin s A La a z
def PoinNz : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La : AddSubgroup (T → I → J → ℂ), GoodLat s A La →
      ∃ a : T → I → J → ℂ, poin s A La a ≠ 0
end PI.ThGW


