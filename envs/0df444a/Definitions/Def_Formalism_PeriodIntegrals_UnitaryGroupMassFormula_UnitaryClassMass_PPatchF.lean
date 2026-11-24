-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PPatchF
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PPatchF
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T15:49:54.050799+00:00
-- url     : https://prove2.me/theorems/5f10b1ac-7fa6-4841-bfc0-07dc54307105
-- title:
--   PPatch F
-- statement:
--   Definitions and structural lemmas for PPatch F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PPatchF.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
section Eps
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def adT (T : Set (HeightOneSpectrum (𝓞 F))) : AF F := (show Ainf F × Af F from ((0 : Ainf F), evT T))
variable (E) in

def epsT (T : Set (HeightOneSpectrum (𝓞 F))) : AF F ⊗[F] E := adT T ⊗ₜ[F] (1 : E)
end Eps
end PI.UnitaryGroupMassFormula.UJClassMass
end


