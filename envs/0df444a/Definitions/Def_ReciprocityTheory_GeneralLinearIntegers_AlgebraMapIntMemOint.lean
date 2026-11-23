-- Prove2me | Definitions.Def_ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint
-- name    : ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:04.930814+00:00
-- url     : https://prove2.me/theorems/29297f14-a782-440f-b983-db86f0024914
-- title:
--   Algebra Map Int Mem Oint
-- statement:
--   Definitions and structural lemmas for Algebra Map Int Mem Oint, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeneralLinearIntegers/AlgebraMapIntMemOint.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct
variable {F : Type} [Field F] [NumberField F]
def Oint (F : Type) [Field F] [NumberField F] : Set (FiniteAdeleRing (𝓞 F) F) :=
  {x | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}
end ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact


