-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_ExceptionalCharacterCondition
-- name    : Development_AutomorphicArithmetic_QuadraticCharacters_ExceptionalCharacterCondition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:36.546622+00:00
-- url     : https://prove2.me/theorems/2a242fb3-43ff-4887-9416-26a27ef7830b
-- title:
--   Exceptional Character Condition
-- statement:
--   Definitions and structural lemmas for Exceptional Character Condition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/QuadraticCharacters/ExceptionalCharacterCondition.lean

import Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_PreHostA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction MeasureTheory
namespace HostParam
noncomputable def prim {N : ℕ} (χ : DirichletCharacter ℂ N) : PrimChar :=
  ⟨χ.conductor, χ.primitiveCharacter⟩
noncomputable def GP (ψ : PrimChar) (y : ℝ) : ℂ :=
  if h : ψ.1 = 0 then 0 else
    haveI : NeZero ψ.1 := ⟨h⟩
    Gfun ψ.2 y
noncomputable def kappaP (ψ : PrimChar) : ℂ :=
  if h : ψ.1 = 0 then 0 else
    haveI : NeZero ψ.1 := ⟨h⟩
    logDerivAtOne ψ.2
noncomputable def Xprime (T : HostType) (x : ℝ) : ℝ := Real.exp (x ^ (T.eps / 3))
namespace PreHost
variable {T : HostType} {X x : ℝ} (P : PreHost T X x)
noncomputable def ch : DirichletCharacter ℂ P.E.N := P.E.chOf P.d P.d_dvd
def Xplus : Set (DirichletCharacter ℂ P.E.N) :=
  {χ | ∃ hχ : χ ∈ P.E.chars, (∀ g ∈ P.A0, P.E.toGalChar χ hχ g = 1) ∧
    ∀ u ∈ P.E.inertiaUnits P.d, χ (u : ZMod P.E.N) = 1}
def fixedA0Chars : Set PrimChar :=
  {ψ | ∃ (χ : DirichletCharacter ℂ P.E.N) (hχ : χ ∈ P.E.chars),
    (∀ g ∈ P.A0, P.E.toGalChar χ hχ g = 1) ∧ prim χ = ψ}
def Xminus : Set (DirichletCharacter ℂ P.E.N) := {χ | ∃ ξ ∈ P.Xplus, χ = P.ch * ξ}
def bounded : Set PrimChar :=
  {ψ | ∃ χ ∈ P.Xplus, prim χ = ψ ∧ ψ ∉ T.kept} ∪ {ψ | ∃ χ ∈ P.Xminus, prim χ = ψ}
def BoundedCharsPointwise : Prop := ∀ ψ ∈ P.bounded, ‖GP ψ x‖ ≤ x ^ (1 / 2 + T.eps)
def BoundedCharsMeanSquare : Prop :=
  ∑ᶠ (ψ : PrimChar) (_ : ψ ∈ P.bounded),
      ∫ y in (X ^ (1 / (T.J : ℝ)))..X, ‖GP ψ y‖ ^ 2 * y ^ (-1 - 2 * T.eps) / y ≤ 1
end PreHost
structure VVFun where
  VV : AbField → ℕ → ENNReal
  mono : ∀ E, Monotone (VV E)
structure Host (T : HostType) (VV : VVFun) (X x : ℝ) extends PreHost T X x where

  kept_sub : ∀ κ ∈ T.kept, ∃ χ ∈ toPreHost.Xplus, prim χ = κ

  character_prime_sum_bound : ∀ χ ∈ E.chars, ∀ y : ℝ, Xprime T x / 3 ≤ y →
    ‖GP (prim χ) y‖ ≤ y * Real.exp (-(T.cA * x ^ (T.eps / 8)))

  character_kappa_power_bound : ‖kappaP (prim toPreHost.ch)‖ ≤ x ^ T.eps
  bounded_chars_log_bound : ∀ ψ ∈ toPreHost.bounded, ‖kappaP ψ‖ ≤ T.CB * Real.log X

  first_or_second_condition : toPreHost.BoundedCharsPointwise ∨ toPreHost.BoundedCharsMeanSquare

  exceptional_character_condition : match T.psK with
    | some κ => prim ps = κ
    | none => prim ps ∉ T.kept

  ha11 : VV.VV E (T.t x) ≤ ENNReal.ofReal (Real.exp (x ^ T.eps) ^ (1 / 2 : ℝ))
structure HostFamily (T : HostType) (VV : VVFun) (X : ℝ) (S : Set ℝ) where
  host : ∀ x ∈ S, Host T VV X x
  second_clause_independent_of_x : ∀ x hx x' hx', ¬ (host x hx).toPreHost.BoundedCharsPointwise →
    let H := host x hx
    let H' := host x' hx'
    H.d = H'.d ∧ H.qs = H'.qs ∧ prim H.ps = prim H'.ps ∧
      H.toPreHost.fixedA0Chars = H'.toPreHost.fixedA0Chars
end HostParam


