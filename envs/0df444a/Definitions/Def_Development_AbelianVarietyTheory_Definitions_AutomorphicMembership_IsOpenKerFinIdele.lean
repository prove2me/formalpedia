-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsOpenKerFinIdele
-- name    : Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsOpenKerFinIdele
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:46.939777+00:00
-- url     : https://prove2.me/theorems/a80e7cb8-167d-4dd1-a7a0-47907b3f5945
-- title:
--   Is Open Ker Fin Idele
-- statement:
--   Definitions and structural lemmas for Is Open Ker Fin Idele, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsOpenKerFinIdele.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology
open scoped ContDiff
namespace GlobalTheory.CuspRep
variable {ι : Type} [Fintype ι]
def expU (z : ι → ℂ) : (ι → ℂ)ˣ :=
  ⟨fun i => Complex.exp (z i), fun i => Complex.exp (-z i),
    by funext i; simp [← Complex.exp_add], by funext i; simp [← Complex.exp_add]⟩
open Classical in

def extZero (ψ : (ι → ℂ)ˣ →* ℂˣ) (x : ι → ℂ) : ℂ := if h : IsUnit x then (ψ h.unit : ℂˣ) else 0
end GlobalTheory.CuspRep


