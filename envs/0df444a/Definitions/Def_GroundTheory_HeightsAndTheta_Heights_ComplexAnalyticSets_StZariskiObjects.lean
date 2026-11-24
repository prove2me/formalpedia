-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:35.887744+00:00
-- url     : https://prove2.me/theorems/2e752555-6110-45e1-969e-ee3e194da504
-- title:
--   St Zariski Objects
-- statement:
--   Definitions and structural lemmas for St Zariski Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StZariskiObjects.lean

import Mathlib
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
open MvPolynomial Topology Filter
noncomputable section
def holGermValue {σ : Type} [Fintype σ] (w : σ → ℂ) : holGerms w →+* ℂ :=
  (Germ.valueRingHom (x := w)).comp (holGerms w).subtype
def holGermPointIdeal {σ : Type} [Fintype σ] (w : σ → ℂ) : Ideal (holGerms w) :=
  RingHom.ker (holGermValue w)
def polyPointIdeal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    Ideal (MvPolynomial σ ℂ ⧸ I) :=
  (RingHom.ker (MvPolynomial.eval w)).map (Ideal.Quotient.mk I)
def germQuotPointIdeal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    Ideal (holGerms w ⧸ I.map (polyGerm w)) :=
  (holGermPointIdeal w).map (Ideal.Quotient.mk _)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


