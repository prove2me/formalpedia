-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:16:59.584494+00:00
-- url     : https://prove2.me/theorems/6c9bff55-61f2-4102-9dd5-7e4cad3d2c64
-- title:
--   Rule GD
-- statement:
--   Definitions and structural lemmas for Rule GD, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.RuleGD
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
def cj (g gi : A) (h : g * gi = 1) (h' : gi * g = 1) : A →+* A where
  toFun x := gi * x * g
  map_one' := by simp [h']
  map_mul' x y := by
    simp only [mul_assoc]
    rw [← mul_assoc g gi (y * g), h, one_mul]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]
section cjlemmas
variable (g gi : A) (h : g * gi = 1) (h' : gi * g = 1)
end cjlemmas
section fnsmem
variable (L : LevelData A r)
end fnsmem
end Formalism.FourierDecayAlt.P.RuleGD
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD
end Formalism.FourierDecayAlt.P


