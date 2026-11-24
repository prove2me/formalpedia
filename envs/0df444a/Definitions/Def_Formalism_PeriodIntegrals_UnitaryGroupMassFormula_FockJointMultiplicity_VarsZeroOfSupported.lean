-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:35.310425+00:00
-- url     : https://prove2.me/theorems/9042233c-69d1-403d-89c1-190f4f6f34d8
-- title:
--   Vars Zero Of Supported
-- statement:
--   Definitions and structural lemmas for Vars Zero Of Supported, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
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
namespace PI.FJMA
open PI.FJM
section Generic
variable {σ : Type}
def FreeOf (S : Set σ) (G : MvPolynomial σ ℂ) : Prop := ∀ e ∈ G.support, ∀ v ∈ S, e v = 0
end Generic
section Blocks
variable {σ : Type}
abbrev blkP {m n : ℕ} (ι : Fin m × Fin n → σ) (α : Fin m → ℕ) : MvPolynomial σ ℂ :=
  shapeProd (Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)) (List.ofFn α)
end Blocks
section Line
variable (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)
end Line
end PI.FJMA


