-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
-- name    : GroundTheory_AutomorphicForms_InductionParabolicLocal
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:01:58.724233+00:00
-- url     : https://prove2.me/theorems/4988feca-23d2-4b9e-b530-3af04a7d5893
-- title:
--   Induction Parabolic Local
-- statement:
--   Definitions and structural lemmas for Induction Parabolic Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (F) (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
def rankTorus (e : ℕ) : GL (Fin n) F :=
  torusPow F n fun i => -((e * blockRank β i : ℕ) : ℤ)
variable {F n β}
variable (F n β) in

def unipotentCompact (e : ℕ) : Subgroup (unipotentRadical F n β) :=
  ((integralGL F n).comap (MulAut.conj (rankTorus F n β e)).toMonoidHom).subgroupOf
    (unipotentRadical F n β)
def conjHomeomorph (t : GL (Fin n) F) : GL (Fin n) F ≃ₜ GL (Fin n) F :=
  (Homeomorph.mulLeft t).trans (Homeomorph.mulRight t⁻¹)
end Parabolic
end GroundTheory.Automorphic


