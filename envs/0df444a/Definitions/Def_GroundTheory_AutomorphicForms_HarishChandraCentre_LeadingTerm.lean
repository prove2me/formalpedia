-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:07:56.148722+00:00
-- url     : https://prove2.me/theorems/166d9e01-f10e-5038-8dd3-766043423a76
-- title:
--   Leading Term
-- statement:
--   Definitions and structural lemmas for Leading Term, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
noncomputable abbrev polyLE (n d : ℕ) : Submodule ℂ (MvPolynomial (Fin n) ℂ) := restrictTotalDegree (Fin n) ℂ d
noncomputable def diagMain (w : List (Fin n × Fin n)) : MvPolynomial (Fin n) ℂ := by
  classical
  exact if ∀ a ∈ w, a.1 = a.2 then (w.map fun a => X a.1).prod else 0
end GroundTheory.Automorphic.HarishChandra


