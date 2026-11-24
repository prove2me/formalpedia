-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExist
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExist
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:02.969514+00:00
-- url     : https://prove2.me/theorems/bbcba68f-0dad-4e7a-b848-9e06ed916c7c
-- title:
--   PTwisted Dual Gens Exist
-- statement:
--   Definitions and structural lemmas for PTwisted Dual Gens Exist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExist.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
section Chart
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω] {τ : Type*}
  {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
def TwistedDualGensExist.latSub {x : τ → Ω} (B : ChartBundle O x r E) (c : τ) :
    Submodule (chartRing O x c) E where
  carrier := B.lat c
  add_mem' := (B.lat c).add_mem
  zero_mem' := (B.lat c).zero_mem
  smul_mem' a e he := B.stable c a a.2 e he
def TwistedDualGensExist.dualSub {x : τ → Ω} (B : ChartBundle O x r E) (c : τ) :
    Submodule (chartRing O x c) (Module.Dual Ω E) where
  carrier := {ψ | ∀ v ∈ B.lat c, ψ v ∈ chartRing O x c}
  add_mem' {ψ χ} hψ hχ v hv := by
    simpa using add_mem (hψ v hv) (hχ v hv)
  zero_mem' v _ := by simp
  smul_mem' a ψ hψ v hv := by
    show ((a : Ω) • ψ) v ∈ _
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact mul_mem a.2 (hψ v hv)
end Chart
section Segre
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
  {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
end Segre
end
end GroundTheory.Heights₂.Heights.NumbersDVR


