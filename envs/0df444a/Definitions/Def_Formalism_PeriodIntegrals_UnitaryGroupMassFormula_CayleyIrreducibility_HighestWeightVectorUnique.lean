-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T11:17:17.477591+00:00
-- url     : https://prove2.me/theorems/d5c3b827-0819-4fa9-a422-1295a0cf852b
-- title:
--   Highest Weight Vector Unique
-- statement:
--   Definitions and structural lemmas for Highest Weight Vector Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighestWeightVectorUnique.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLine
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf MvPolynomial
section Common
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
def sl (τ₀ : ι) (x : ι × Fin n × Fin n → ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  aeval fun v => if v.1 = τ₀ then X v.2 else C (x v)
end Common
section UniqPf
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
end UniqPf
section GenPf
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
end GenPf
end Formalism.L2.SG.Pf.ColDictValCPf


