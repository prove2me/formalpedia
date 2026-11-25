-- Prove2me | Definitions.Def_SNumbers_Injectivity
-- name    : SNumbers_Injectivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:39:12.060723+00:00
-- url     : https://prove2.me/theorems/2fe2d6c2-239b-4b30-9abf-0a47186bfa31
-- title:
--   Injectivity
-- statement:
--   Definitions and structural lemmas for Injectivity, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped Cardinal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
def IsMetricInjection (J : Y →L[𝕜] Z) : Prop :=
  ∀ y, ‖J y‖ = ‖y‖
structure IsMetricSurjection (Q : W →L[𝕜] X) : Prop where
  /-- A metric surjection is a contraction. -/
  norm_le_one : ‖Q‖ ≤ 1
  /-- Every point has preimages of norm arbitrarily close to its own. -/
  exists_preimage_lt : ∀ (x : X) (ε : ℝ), 0 < ε → ∃ w : W, Q w = x ∧ ‖w‖ < ‖x‖ + ε
def Injective (s : Family 𝕜) : Prop :=
  ∀ {X Y Z : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
      (S : X →L[𝕜] Y) (J : Y →L[𝕜] Z), IsMetricInjection J → ∀ n : ℕ,
    s (J.comp S) n = s S n
def Surjective (s : Family 𝕜) : Prop :=
  ∀ {W X Y : Type u} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      (S : X →L[𝕜] Y) (Q : W →L[𝕜] X), IsMetricSurjection Q → ∀ n : ℕ,
    s (S.comp Q) n = s S n
end SNumbers


