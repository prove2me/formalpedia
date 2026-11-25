-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ResidOfMem
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ResidOfMem
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:07:48.016848+00:00
-- url     : https://prove2.me/theorems/13b2a597-a73b-478c-a2aa-ad1c3dd0479e
-- title:
--   Resid Of Mem
-- statement:
--   Definitions and structural lemmas for Resid Of Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ResidOfMem.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsRestLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
noncomputable section
section RestrictGenAux
variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {K' : Type} [Field K'] [Algebra F K']
  (R : Subalgebra F Ω) (σ : R →ₐ[F] K')
open Classical in

def RestrictGen.resid (a : Ω) : K' := if h : a ∈ R then σ ⟨a, h⟩ else 0
end RestrictGenAux
end
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


