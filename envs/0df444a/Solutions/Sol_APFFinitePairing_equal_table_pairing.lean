-- Prove2me | solution 1 for APFFinitePairing.equal_table_pairing
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-10-02T13:14:23.837635+00:00
-- url     : https://prove2.me/submissions/141219d6-7826-455e-82ac-1ed278ecca98

import Definitions.Def_APFFinitePairing_rightEquiv
import Definitions.Def_APFFinitePairing_RightSpace
import Definitions.Def_APFFinitePairing_LeftRad
import Definitions.Def_APFFinitePairing_leftEquiv
import Definitions.Def_APFFinitePairing_LeftSpace
import Definitions.Def_APFFinitePairing_RightRad
import Definitions.Def_APFFinitePairing_pairing
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open APFFinitePairing
variable {I J : Type*} [Fintype I] [Fintype J]
theorem solution (M N : I → J → ℝ) (h : M=N)
    (a : LeftSpace M) (b : RightSpace M) :
    pairing N (leftEquiv M N h a) (rightEquiv M N h b) = pairing M a b := by
  subst N; rfl
