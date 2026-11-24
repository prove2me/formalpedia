-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:21.507124+00:00
-- url     : https://prove2.me/theorems/0fd1cc63-4f27-4ca9-846a-2c548c9fca63
-- title:
--   Kronecker One Right Swap
-- statement:
--   Definitions and structural lemmas for Kronecker One Right Swap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
namespace PI.FockOneDegW.Swap
open PI.FockOneDegW PI.FockOneDegW.Diag
section Transport
variable {m n : ℕ} {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
end Transport
section Rename
variable {σ τ : Type*} (f : σ ≃ τ)
end Rename
variable {p q r s : ℕ}
abbrev sw (p q r s : ℕ) : Ln p q r s ≃ Ln r s p q := Equiv.prodComm _ _
def swL (p q r s : ℕ) : Pol p q r s →ₗ[ℂ] Pol r s p q := (rename (sw p q r s)).toLinearMap
end PI.FockOneDegW.Swap


