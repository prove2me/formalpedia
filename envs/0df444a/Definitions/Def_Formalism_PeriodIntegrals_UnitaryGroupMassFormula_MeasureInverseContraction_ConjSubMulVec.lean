-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_ConjSubMulVec
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_ConjSubMulVec
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:01:23.408796+00:00
-- url     : https://prove2.me/theorems/7090f764-3d8a-4b28-abaa-ee9e2acaba09
-- title:
--   Conj Sub Mul Vec
-- statement:
--   Definitions and structural lemmas for Conj Sub Mul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/ConjSubMulVec.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
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
namespace PI.NMeasInv.UnitaryGroupMassFormula
section Tri
variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG
omit hG in

def Sb (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ)
    (i : Fin n) : ℝ :=
  ∑ b, ((∑ c, ‖hJ ε (f c) y * hJ ε (f b) ((g - 1) *ᵥ e c)‖ +
      ∑ c, ‖hJ ε (e c) y * hJ ε (f b) ((g - 1) *ᵥ f c)‖ +
      ‖hJ ε (f b) ((g - 1) *ᵥ Pw ε e f y)‖) * ‖e b i‖) +
    ∑ b, (∑ c, ‖hJ ε (e c) y * hJ ε (e b) ((g - 1) *ᵥ f c)‖) * ‖f b i‖ +
    ∑ c, ‖hJ ε (e c) y‖ * ‖Pw ε e f ((g - 1) *ᵥ f c) i‖
end Tri
end PI.NMeasInv.UnitaryGroupMassFormula


