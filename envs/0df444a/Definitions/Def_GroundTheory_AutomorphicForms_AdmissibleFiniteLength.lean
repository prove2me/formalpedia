-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleFiniteLength
-- name    : GroundTheory_AutomorphicForms_AdmissibleFiniteLength
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T11:54:12.085421+00:00
-- url     : https://prove2.me/theorems/75af88f7-a3dc-44a9-a66c-48ac577577ee
-- title:
--   Admissible Finite Length
-- statement:
--   Definitions and structural lemmas for Admissible Finite Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleFiniteLength.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
end Parabolic
end GroundTheory.Automorphic


