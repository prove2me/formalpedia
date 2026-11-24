-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteModuloIntegral
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteModuloIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:22.689917+00:00
-- url     : https://prove2.me/theorems/a03f49ab-cb3a-4ddb-abc0-84565bf26504
-- title:
--   PFinite Modulo Integral
-- statement:
--   Definitions and structural lemmas for PFinite Modulo Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteModuloIntegral.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteModuloIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
def germCompRingHom {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    Germ (𝓝 (L x)) ℂ →+* Germ (𝓝 x) ℂ where
  toFun s := s.compTendsto L (L.continuous.tendsto x)
  map_one' := rfl
  map_mul' s t := Germ.inductionOn₂ s t fun _ _ => rfl
  map_zero' := rfl
  map_add' s t := Germ.inductionOn₂ s t fun _ _ => rfl
def holGermsPullback {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    holGerms (L x) →+* holGerms x :=
  ((germCompRingHom x L).comp (holGerms (L x)).subtype).codRestrict (holGerms x) fun s => by
    obtain ⟨b, hb, hbs⟩ := s.2
    refine ⟨b ∘ L, hb.comp (L.analyticAt x), ?_⟩
    show _ = germCompRingHom x L s.1
    rw [← hbs]
    rfl
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


