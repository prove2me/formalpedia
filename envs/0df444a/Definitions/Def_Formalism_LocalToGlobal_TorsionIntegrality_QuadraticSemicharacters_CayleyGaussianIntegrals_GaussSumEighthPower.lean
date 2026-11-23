-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:25.111251+00:00
-- url     : https://prove2.me/theorems/ba42db5a-114e-4ee2-b99d-b45d0fff94ce
-- title:
--   Gauss Sum Eighth Power
-- statement:
--   Definitions and structural lemmas for Gauss Sum Eighth Power, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaussSumEighthPower.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.H
namespace IsQuadFn
variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}
end IsQuadFn
section Quaternion
variable (M : Type*) [AddCommGroup M]
def quatI : (Fin 4 → M) →+ (Fin 4 → M) where
  toFun v := ![-v 1, v 0, -v 3, v 2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> simp <;> abel
def quatJ : (Fin 4 → M) →+ (Fin 4 → M) where
  toFun v := ![-v 2, v 3, v 0, -v 1]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> simp <;> abel
def quatK : (Fin 4 → M) →+ (Fin 4 → M) where
  toFun v := ![-v 3, -v 2, v 1, v 0]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> simp <;> abel
end Quaternion
end Formalism.L2.Th1.H


