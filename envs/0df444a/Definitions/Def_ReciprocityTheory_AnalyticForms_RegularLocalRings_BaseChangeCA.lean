-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:04.741803+00:00
-- url     : https://prove2.me/theorems/2fdd54cc-1542-4491-8a7e-67485dbbe8e4
-- title:
--   Base Change CA
-- statement:
--   Definitions and structural lemmas for Base Change CA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R.BaseChangeC
open MvPolynomial TensorProduct
section FracTensor
variable (ι : Type) (F : Type) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial ι ℚ) F]
  [IsScalarTower ℚ (MvPolynomial ι ℚ) F] [IsFractionRing (MvPolynomial ι ℚ) F]
  (C : Type) [Field C] [Algebra ℚ C]
end FracTensor
section Red
attribute [-instance] DivisionRing.toRatAlgebra
end Red
end ReciprocityTheory.AnForm.R.BaseChangeC


