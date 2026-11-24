-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:25:01.484847+00:00
-- url     : https://prove2.me/theorems/4b86d77f-50d4-4466-a548-ef3e7e1b3335
-- title:
--   PTwist Sections
-- statement:
--   Definitions and structural lemmas for PTwist Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
section Loc
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type*} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
end Loc
section Proof
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)
def primeQuotGraded : GradedPMod S N (Poly S N ⧸ primeOf (S := S) y) :=
  quotGraded (primeOf (S := S) y) fun _ hf d => homogeneousComponent_mem_primeOf y hf d
end Proof
end
end GroundTheory.Heights₂.Heights.Kleiman


