-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_OrdFEqOfClassOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_OrdFEqOfClassOf
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:31.851669+00:00
-- url     : https://prove2.me/theorems/0beff266-246c-4680-a0ac-d5a7d3351712
-- title:
--   Ord FEq Of Class Of
-- statement:
--   Definitions and structural lemmas for Ord FEq Of Class Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/OrdFEqOfClassOf.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Theorems.Thm_Neutral_B1_exists_isUniformiserAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
namespace PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
def piU (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ :=
  Classical.choose (exists_isUniformiserAt L v)
def eU (v : HeightOneSpectrum (𝓞 L)) : Ideles L := localIdele L v (piU v)
end PI.AlgValsFin.W


