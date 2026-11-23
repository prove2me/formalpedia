-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:40.477851+00:00
-- url     : https://prove2.me/theorems/a5f650f7-ae29-4def-83f5-26528d33ea67
-- title:
--   Diff Loc
-- statement:
--   Definitions and structural lemmas for Diff Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct Pointwise
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
def DiffLoc_psi (S : Set E) : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F) (inclR (F := F) (Fv F v) '' S)
def DiffLoc_P : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  DiffLoc_psi (E := E) v (Set.range ((↑) : 𝓞 E → E))
end
end PI.LocFramePrimWork


