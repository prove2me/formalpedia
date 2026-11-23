-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:29.682233+00:00
-- url     : https://prove2.me/theorems/a4d49e6c-cb3a-4908-913f-1c4cfaeaf0ec
-- title:
--   Exists Polarized Superlattice Of Riemann Form
-- statement:
--   Definitions and structural lemmas for Exists Polarized Superlattice Of Riemann Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.UnimodOver
open Module
section General
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
end General
def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ Hm.mulVec (star w)).im)
    (fun a b w => by simp [add_dotProduct])
    (fun r a w => by simp [smul_dotProduct])
    (fun a b w => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun r a w => by simp [Matrix.mulVec_smul, dotProduct_smul])
end GlobalTheory.UnimodOver


