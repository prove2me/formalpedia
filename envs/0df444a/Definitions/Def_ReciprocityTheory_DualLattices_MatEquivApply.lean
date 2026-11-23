-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
-- name    : ReciprocityTheory_DualLattices_MatEquivApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:06.206683+00:00
-- url     : https://prove2.me/theorems/eb4d4c07-3b58-4ba5-b371-b4eff3f8f863
-- title:
--   Mat Equiv Apply
-- statement:
--   Definitions and structural lemmas for Mat Equiv Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MatEquivApply.lean

import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R]
def matEquiv {d : ℕ} (P : Matrix (Fin d) (Fin d) R) (hP : IsUnit P.det) :
    (Fin d → R) ≃ₗ[R] (Fin d → R) :=
  LinearEquiv.ofLinear (Matrix.toLin' P) (Matrix.toLin' P⁻¹)
    (by rw [← Matrix.toLin'_mul, mul_nonsing_inv _ hP, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, nonsing_inv_mul _ hP, Matrix.toLin'_one])
end ReciprocityTheory.PGsh.Up


