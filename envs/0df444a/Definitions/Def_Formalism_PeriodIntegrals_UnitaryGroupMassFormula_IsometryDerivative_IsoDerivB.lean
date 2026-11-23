-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_IsoDerivB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_IsoDerivB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:54.935338+00:00
-- url     : https://prove2.me/theorems/d1eca07e-a1ae-4a3a-a7a1-1d429ce9b094
-- title:
--   Iso Deriv B
-- statement:
--   Definitions and structural lemmas for Iso Deriv B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/IsoDerivB.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace PI.IsoDerivBFintype
open PI.IsoDerivB
section expand
variable {T : Type} {N N' : ℕ} (s : T → ℂ) (y' : T → Matrix (Fin N') (Fin N') ℂ)
def gD : FrV T N → MvPolynomial (Idx T N N') ℂ := fun k => ∑ b : Fin N',
    MvPolynomial.C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : Idx T N N')
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) (nu : Lt → YoungDiagram)
end expand
end PI.IsoDerivBFintype


