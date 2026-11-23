-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionExistence_LeOneIffOfMulEqOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionExistence_LeOneIffOfMulEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:45:54.195+00:00
-- url     : https://prove2.me/theorems/c17db506-ef1f-4b39-9317-f777a517fdc5
-- title:
--   Le One Iff Of Mul Eq One
-- statement:
--   Definitions and structural lemmas for Le One Iff Of Mul Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionExistence/LeOneIffOfMulEqOne.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.CompAtExist
open NumberField IsDedekindDomain ReciprocityTheory.Aut
def StepA (L : Type) [Field L] [NumberField L] [IsCMField L] : Prop :=
  ∀ (s : SplitPlace L) (k : L),
    Valued.v (s.i k) = Valued.v (algebraMap L (s.w.adicCompletion L) k)
section
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
def muV (s : SplitPlace L) : Valuation L (WithZero (Multiplicative ℤ)) :=
  (Valued.v : Valuation (s.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ))).comap
    (s.i : L →+* s.v.adicCompletion (maximalRealSubfield L))
end
end PI.CompAtExist


