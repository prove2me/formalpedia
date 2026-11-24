-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalGermIntegrallyClosed
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalGermIntegrallyClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:08.154888+00:00
-- url     : https://prove2.me/theorems/ac15faeb-58ea-4ff0-bdb4-b81d1572e8ea
-- title:
--   PNormal Germ Integrally Closed
-- statement:
--   Definitions and structural lemmas for PNormal Germ Integrally Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalGermIntegrallyClosed.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRueckertNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
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
open MvPolynomial Topology Filter
noncomputable section
namespace NormalGermIntegrallyClosed
def anFun {σ : Type} [Fintype σ] (w : σ → ℂ) : Subring ((σ → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f w}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := analyticAt_const
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := analyticAt_const
  neg_mem' := fun hf => hf.neg
def toGerm {σ : Type} [Fintype σ] (w : σ → ℂ) : anFun w →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (anFun w).subtype).codRestrict (holGerms w) fun u => ⟨u.1, u.2, rfl⟩
end NormalGermIntegrallyClosed
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


