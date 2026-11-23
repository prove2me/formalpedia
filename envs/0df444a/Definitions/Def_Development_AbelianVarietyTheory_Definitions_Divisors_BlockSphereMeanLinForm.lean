-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:08.318797+00:00
-- url     : https://prove2.me/theorems/d2ca36de-f420-4168-9650-7261f8273c90
-- title:
--   Block Sphere Mean Lin Form
-- statement:
--   Definitions and structural lemmas for Block Sphere Mean Lin Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
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
open MvPolynomial NumberField
namespace GlobalTheory.ChowHt.Model
def linForm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) : MvPolynomial (Fin 1 × Fin N) R :=
  ∑ j, C (c j) * X (0, j)
end GlobalTheory.ChowHt.Model


