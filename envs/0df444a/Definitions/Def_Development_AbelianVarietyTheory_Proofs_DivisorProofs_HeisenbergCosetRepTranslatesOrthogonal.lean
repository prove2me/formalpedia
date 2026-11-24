-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergCosetRepTranslatesOrthogonal
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergCosetRepTranslatesOrthogonal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:36.070702+00:00
-- url     : https://prove2.me/theorems/4f39c13d-8cbd-4095-9f1c-a89b99b119e0
-- title:
--   Heisenberg Coset Rep Translates Orthogonal
-- statement:
--   Definitions and structural lemmas for Heisenberg Coset Rep Translates Orthogonal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeisenbergCosetRepTranslatesOrthogonal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryAndSeparates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
namespace GlobalTheory.HeisUnit
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
def entryForm (c : k) (i0 : Fin n) (j : Fin d) : Matrix (Fin n) (Fin d) k →ₗ[k] k where
  toFun Y := c * Y i0 j
  map_add' Y Y' := by simp [mul_add]
  map_smul' a Y := by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
end GlobalTheory.HeisUnit
namespace GlobalTheory.HeisUnit
end GlobalTheory.HeisUnit
namespace GlobalTheory.HeisUnit
end GlobalTheory.HeisUnit


