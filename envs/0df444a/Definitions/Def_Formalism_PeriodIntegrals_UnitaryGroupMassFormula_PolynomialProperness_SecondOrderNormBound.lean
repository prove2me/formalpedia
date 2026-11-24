-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:13:11.465007+00:00
-- url     : https://prove2.me/theorems/e3cdc235-75c5-4456-b60d-86e7644e47e0
-- title:
--   Second Order Norm Bound
-- statement:
--   Definitions and structural lemmas for Second Order Norm Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
namespace PI.PolynomialProperness.CB
def rws {m : ℕ} (i : Fin m) : Fin (i.val + 1) → Fin m := Fin.castLE (Nat.succ_le_of_lt i.isLt)
def cls {m : ℕ} (i j : Fin m) : Fin (i.val + 1) → Fin m := fun t =>
  if t.val < i.val then Fin.castLE (Nat.succ_le_of_lt i.isLt) t else j
def kap (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ) : ℝ := 1 + m * mx P⁻¹
def Kc (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  m.factorial * kap m P ^ m * (1 + (m : ℝ) ^ 2 * mx P * mx P⁻¹)
end PI.PolynomialProperness.CB
namespace PI.PolynomialProperness
end PI.PolynomialProperness


