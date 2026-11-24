-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:12.308796+00:00
-- url     : https://prove2.me/theorems/b0c0d90a-fcf3-40cc-b28e-36db579e4763
-- title:
--   Chart Glue Frame
-- statement:
--   Definitions and structural lemmas for Chart Glue Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrame.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
section FrameGeneric
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
def IsFrameAt (A : Subalgebra ℤ Ω) (r : ℕ) (M : AddSubgroup E) (h : Ω) : Prop :=
  ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
    ∀ e, (∃ n : ℕ, h ^ n • e ∈ M) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, h ^ n * a q ∈ A) ∧ e = ∑ q, a q • b q
end FrameGeneric
section FrameGlue
variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]
  {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}
end FrameGlue
end GroundTheory.Heights₂.Heights.Model


