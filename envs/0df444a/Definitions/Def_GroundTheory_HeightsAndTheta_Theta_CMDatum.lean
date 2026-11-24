-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
-- name    : GroundTheory_HeightsAndTheta_Theta_CMDatum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:54.225966+00:00
-- url     : https://prove2.me/theorems/b0b7f1e3-bbdb-4cb5-b65c-f9f9ce0cd80c
-- title:
--   CMDatum
-- statement:
--   Definitions and structural lemmas for CMDatum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
section Datum
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
include F in

theorem isCMField : IsCMField E := IsCMField.ofCMExtension F E
noncomputable def complexConjOver : E ≃ₐ[F] E :=
  haveI := isCMField F E
  AlgEquiv.ofRingEquiv (f := (IsCMField.complexConj E).toRingEquiv) fun x => by
    have h : ((CMExtension.equivMaximalRealSubfield F E x : maximalRealSubfield E) : E) =
        algebraMap F E x := CMExtension.equivMaximalRealSubfield_apply F E x
    rw [← h]
    exact IsCMField.complexConj_apply_eq_self E _
variable {F E}
variable (F E)
variable {F E}
variable (F E)
end Datum
end GroundTheory.Heights₂.Theta


